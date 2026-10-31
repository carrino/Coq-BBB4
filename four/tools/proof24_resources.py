"""Linux/WSL/cgroup resource limits; no external commands at import time."""
from __future__ import annotations

import json
import ctypes
import os
from pathlib import Path
import resource
import signal
import subprocess
import sys
import threading
import time

from proof24_common import PHASES

MIB = 1024 * 1024


def meminfo():
    result = {}
    for line in Path('/proc/meminfo').read_text().splitlines():
        name, value = line.split(':', 1)
        if value.strip().endswith('kB'):
            result[name] = int(value.split()[0]) * 1024
    return result


def cgroups():
    """Visible root and nested process cgroups, v2 and conventional v1 mount."""
    result = {Path('/sys/fs/cgroup')}
    for line in Path('/proc/self/cgroup').read_text().splitlines():
        _, controllers, suffix = line.split(':', 2)
        suffix = suffix.lstrip('/')
        if not controllers:
            result.add(Path('/sys/fs/cgroup') / suffix)
        elif 'memory' in controllers.split(','):
            result.add(Path('/sys/fs/cgroup/memory') / suffix)
    # A parent cgroup can have a tighter cap than the current subgroup.
    for root in list(result):
        while root.is_relative_to('/sys/fs/cgroup'):
            result.add(root)
            if root == Path('/sys/fs/cgroup'):
                break
            root = root.parent
    return sorted(result)


def memory_snapshot():
    info = meminfo()
    total = info['MemTotal']
    available = info.get('MemAvailable', info['MemFree'])
    rows = []
    for root in cgroups():
        for limit_name, use_name in [('memory.max', 'memory.current'),
                                     ('memory.limit_in_bytes', 'memory.usage_in_bytes')]:
            limit_file, use_file = root / limit_name, root / use_name
            try:
                raw = limit_file.read_text().strip()
                if raw == 'max':
                    continue
                limit, used = int(raw), int(use_file.read_text())
                if limit <= 0 or limit >= 1 << 60:
                    continue
                stats = {}
                try:
                    stats = {k: int(v) for k, v in (line.split() for line in
                             (root / 'memory.stat').read_text().splitlines())}
                except FileNotFoundError:
                    pass
                if limit_name == 'memory.max' and 'file' in stats and 'shmem' in stats:
                    cache = max(0, stats.get('file', 0) - stats.get('shmem', 0))
                    page_cache = stats.get('inactive_file', 0) + stats.get('active_file', 0)
                    dirty = stats.get('file_dirty', 0) + stats.get('file_writeback', 0)
                elif limit_name != 'memory.max' and 'total_cache' in stats and 'total_shmem' in stats:
                    cache = max(0, stats['total_cache'] - stats['total_shmem'])
                    page_cache = stats.get('total_inactive_file', 0) + stats.get('total_active_file', 0)
                    dirty = stats.get('total_dirty', 0) + stats.get('total_writeback', 0)
                elif limit_name != 'memory.max' and 'total_cache' not in stats and 'shmem' in stats:
                    cache = max(0, stats.get('cache', 0) - stats['shmem'])
                    page_cache = stats.get('inactive_file', 0) + stats.get('active_file', 0)
                    dirty = stats.get('dirty', 0) + stats.get('writeback', 0)
                else:
                    cache = page_cache = dirty = 0  # Cannot safely exclude v1 shmem.
                reclaimable = min(used, max(0, min(cache, page_cache) - dirty))
                headroom = min(limit, max(0, limit - used + reclaimable))
                rows.append({'path': str(root), 'limit_bytes': limit, 'used_bytes': used,
                             'clean_file_cache_bytes': reclaimable,
                             'cache_adjusted_headroom_bytes': headroom})
                total = min(total, limit)
                available = min(available, headroom)
            except FileNotFoundError:
                continue
    reserve = max(1536 * MIB, total // 10)
    return {'effective_limit_bytes': total, 'available_bytes': available,
            'reserve_bytes': reserve, 'usable_bytes': max(0, available - reserve),
            'cgroups': rows, 'linux_memtotal_bytes': info['MemTotal']}


def phase_limits(phase, jobs, snapshot=None, profiles=None):
    snap = memory_snapshot() if snapshot is None else snapshot
    profile = (PHASES if profiles is None else profiles)[phase]
    address_space = profile['address_space_mib'] * MIB
    rss_guard = profile['rss_guard_mib'] * MIB
    # Address space and resident RAM have different roles. The RSS budgets cap
    # concurrency; the AS limit also fits the visible machine/cgroup limit.
    machine_budget = snap.get('effective_limit_bytes', snap['usable_bytes']) - snap.get('reserve_bytes', 0)
    workers = min(jobs, profile['workers'], os.cpu_count() or 1,
                  snap['usable_bytes'] // rss_guard)
    if workers < 1 or address_space > machine_budget:
        raise ValueError('Insufficient current RAM headroom for phase ' + phase + ': ' + json.dumps(snap))
    return {'workers': workers, 'address_space_bytes': address_space,
            'rss_guard_bytes': rss_guard, 'memory': snap}


def filesystem_type(path):
    target = Path(path).resolve()
    best = None
    for line in Path('/proc/self/mountinfo').read_text().splitlines():
        before, after = line.split(' - ', 1)
        # Linux mountinfo octal escapes include spaces in mountpoint names.
        mountpoint = before.split()[4]
        for encoded, literal in [('\\040', ' '), ('\\011', '\t'), ('\\134', '\\')]:
            mountpoint = mountpoint.replace(encoded, literal)
        p = Path(mountpoint)
        if target.is_relative_to(p) and (best is None or len(p.parts) > best[0]):
            best = (len(p.parts), after.split()[0])
    return best[1] if best else None


def check_disk(path, reserve_gib):
    p = Path(path).resolve()
    while not p.exists():
        p = p.parent
    kind = filesystem_type(p)
    if kind in ('tmpfs', 'ramfs'):
        raise ValueError('Build tree/logs must be on a disk filesystem, not ' + str(kind))
    stat = os.statvfs(p)
    free = stat.f_bavail * stat.f_frsize
    if free < reserve_gib * 1024 ** 3:
        raise ValueError('Insufficient disk reserve at ' + str(p))
    return {'filesystem': kind, 'free_bytes': free}


def process_table():
    result = {}
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():
            continue
        try:
            # The command name can contain parentheses and spaces.
            fields = (p / 'stat').read_text().rsplit(')', 1)[1].split()
            result[int(p.name)] = {'ppid': int(fields[1]), 'session': int(fields[3]),
                'start': int(fields[19]), 'rss': int(fields[21]) * os.sysconf('SC_PAGE_SIZE'),
                'state': fields[0]}
        except (OSError, ValueError, IndexError):
            continue
    return result


def owned_processes(leader, table):
    owned = {pid for pid, row in table.items() if row['session'] == leader}
    owned.add(leader)
    changed = True
    while changed:
        extra = {pid for pid, row in table.items() if row['ppid'] in owned} - owned
        changed = bool(extra)
        owned.update(extra)
    return owned & table.keys()


def matching_known(known, table):
    return {pid for pid, start in known.items() if pid in table and table[pid]['start'] == start}


def signal_owned(leader, signum, known=None):
    table = process_table()
    pids = owned_processes(leader, table) | matching_known(known or {}, table)
    # Signal descendants first; the supervisor retains subreaper ownership.
    for pid in sorted(pids - {leader}):
        try:
            os.kill(pid, signum)
        except ProcessLookupError:
            pass
    if leader in pids:
        try:
            os.kill(leader, signum)
        except ProcessLookupError:
            pass


class CommandBatch:
    """Cancel all current owned supervisors when any batch member fails."""
    def __init__(self):
        self.cancelled = threading.Event()
        self.lock = threading.Lock()
        self.processes = {}

    def register(self, process):
        with self.lock:
            self.processes[process.pid] = process
        if self.cancelled.is_set():
            raise RuntimeError('Compile batch was cancelled')

    def unregister(self, process):
        with self.lock:
            self.processes.pop(process.pid, None)

    def cancel(self):
        self.cancelled.set()
        with self.lock:
            processes = list(self.processes.values())
        for process in processes:
            if process.poll() is None:
                signal_owned(process.pid, signal.SIGTERM)


def stop_supervisor(process, known):
    signal_owned(process.pid, signal.SIGTERM, known)
    deadline = time.monotonic() + 10
    while True:
        table = process_table()
        owned = owned_processes(process.pid, table) | matching_known(known, table)
        known.update({pid: table[pid]['start'] for pid in owned})
        # Leave the supervisor alive so it can reap all adopted descendants,
        # including children which changed process group or session.
        for pid in owned - {process.pid}:
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        code = process.poll()
        if code is not None and not matching_known(known, process_table()):
            return
        if time.monotonic() > deadline:
            raise RuntimeError('Owned processes did not terminate; supervisor retains ownership: '
                               + str(sorted(owned)))
        time.sleep(0.05)


def run_capped(command, cwd, env, log, limits, timeout, batch=None):
    """Own the complete child lifetime and cancel every batch group on failure."""
    if batch is not None and batch.cancelled.is_set():
        raise RuntimeError('Compile batch was cancelled before launch')
    started = time.monotonic()
    maximum = 0
    known = {}
    with Path(log).open('w') as stream:
        wrapper = [sys.executable, str(Path(__file__).resolve()), '--exec',
                   str(limits['address_space_bytes']), *command]
        process = subprocess.Popen(wrapper, cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True,
                                   )
        try:
            if batch is not None:
                batch.register(process)
            while True:
                table = process_table()
                owned = owned_processes(process.pid, table) | matching_known(known, table)
                known.update({pid: table[pid]['start'] for pid in owned})
                rss = sum(table[pid]['rss'] for pid in owned)
                maximum = max(maximum, rss)
                if any(table[pid]['session'] != process.pid for pid in owned):
                    raise RuntimeError('Owned descendant escaped its session: ' + str(log))
                if batch is not None and batch.cancelled.is_set():
                    raise RuntimeError('Compile batch was cancelled: ' + str(log))
                if rss > limits['rss_guard_bytes']:
                    raise RuntimeError('Child session exceeded RSS guard: ' + str(log))
                if time.monotonic() - started > timeout:
                    raise RuntimeError('Command timed out: ' + str(log))
                # Leave the machine's configured reserve free, even if another job starts.
                snapshot = memory_snapshot()
                if snapshot['available_bytes'] < snapshot['reserve_bytes'] // 2:
                    raise RuntimeError('Machine RAM headroom fell below safety reserve: ' + str(log))
                for output_root in (Path(cwd), Path(log).parent):
                    stat = os.statvfs(output_root)
                    if stat.f_bavail * stat.f_frsize < 1024 ** 3:
                        raise RuntimeError('Disk headroom fell below 1 GiB: ' + str(log))
                code = process.poll()
                if code is not None:
                    if matching_known(known, process_table()):
                        raise RuntimeError('Command supervisor exited with remaining descendants: ' + str(log))
                    break
                time.sleep(0.1)
            if process.returncode:
                raise RuntimeError('Command failed, exit ' + str(process.returncode) + ': ' + str(log))
        except BaseException:
            if batch is not None:
                batch.cancel()
            stop_supervisor(process, known)
            raise
        finally:
            if batch is not None:
                batch.unregister(process)
    return {'exit_code': process.returncode, 'elapsed_seconds': round(time.monotonic() - started, 3),
            'sampled_maximum_owned_process_rss_bytes': maximum, 'command': command,
            'ownership': 'Linux subreaper; complete descendant lifetime',
            'log_sha256_required_separately': True}


def supervise(command, cap):
    """A Linux subreaper owns detached/orphan descendants until they are gone."""
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER
        raise OSError(ctypes.get_errno(), 'Could not enable command subreaper')
    resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    cancelled = [False]
    signal.signal(signal.SIGTERM, lambda *_: cancelled.__setitem__(0, True))
    signal.signal(signal.SIGINT, lambda *_: cancelled.__setitem__(0, True))
    leader = os.fork()
    if leader == 0:
        signal.signal(signal.SIGTERM, signal.SIG_DFL)
        signal.signal(signal.SIGINT, signal.SIG_DFL)
        os.execve(command[0], command, os.environ)
    status = None
    reason = None
    known = {}
    while True:
        table = process_table()
        owned = owned_processes(os.getpid(), table) - {os.getpid()}
        known.update({pid: table[pid]['start'] for pid in owned})
        if any(table[pid]['session'] != os.getpid() for pid in owned):
            reason = 'unexpected descendant escaped the command session'
        while True:
            try:
                pid, child_status = os.waitpid(-1, os.WNOHANG)
            except ChildProcessError:
                break
            if not pid:
                break
            if pid == leader:
                status = child_status
            else:
                reason = 'unexpected orphan descendant was adopted by the command supervisor'
        table = process_table()
        owned = owned_processes(os.getpid(), table) - {os.getpid()}
        known.update({pid: table[pid]['start'] for pid in owned})
        if status is not None and owned:
            reason = 'command leader exited with live descendants'
        if cancelled[0]:
            reason = 'command supervisor was cancelled'
        if reason is not None:
            for pid in owned | matching_known(known, table):
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            # Reap adopted children; do not exit and transfer them to PID 1.
            if not owned and not matching_known(known, table):
                print(reason, file=sys.stderr, flush=True)
                return 125
        elif status is not None and not owned:
            return os.waitstatus_to_exitcode(status)
        time.sleep(0.05)


if __name__ == '__main__':
    if len(sys.argv) < 4 or sys.argv[1] != '--exec':
        raise SystemExit('This module is an internal resource wrapper')
    sys.exit(supervise(sys.argv[3:], int(sys.argv[2])))
