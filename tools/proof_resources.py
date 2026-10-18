#!/usr/bin/env python3
"""Size CPU-bound proof jobs from physical cores and available memory.

Linux containers are capped by their cgroup v2 limits. macOS uses vm_stat's
free, inactive and speculative pages; active, wired and compressed pages do
not count as available. Unknown memory information selects one job.
"""
import argparse
import os
from pathlib import Path
import platform
import re
import subprocess

GIB = 1024 ** 3


def command(*args):
    try:
        return subprocess.check_output(args, text=True, stderr=subprocess.DEVNULL)
    except (OSError, subprocess.CalledProcessError):
        return ''


def read(path):
    try:
        return Path(path).read_text().strip()
    except OSError:
        return ''


def cgroup_paths():
    """The process's v2 group and visible ancestors, including root limits."""
    for line in read('/proc/self/cgroup').splitlines():
        if line.startswith('0::'):
            root = Path('/sys/fs/cgroup')
            current = root / line[3:].lstrip('/')
            if '..' in current.parts:
                return
            while True:
                yield current
                if current == root:
                    return
                current = current.parent


def mac_available(text):
    page = re.search(r'page size of (\d+) bytes', text)
    if not page:
        return None
    pages = dict(re.findall(r'^(Pages [\w ]+):\s*(\d+)\.', text, re.M))
    names = ['Pages free', 'Pages inactive', 'Pages speculative']
    if any(name not in pages for name in names):
        return None
    return int(page[1]) * sum(int(pages[name]) for name in names)


def available_memory():
    if platform.system() == 'Darwin':
        return mac_available(command('vm_stat'))
    match = re.search(r'^MemAvailable:\s*(\d+) kB', read('/proc/meminfo'), re.M)
    available = int(match[1]) * 1024 if match else None
    for group in cgroup_paths():
        maximum, current = read(group / 'memory.max'), read(group / 'memory.current')
        if maximum.isdecimal() and current.isdecimal():
            # Clean file cache from earlier proof builds can be reclaimed.
            # Counting it as pinned memory needlessly removes walk workers.
            stat = dict(re.findall(r'^(\w+)\s+(\d+)$',
                                   read(group / 'memory.stat'), re.M))
            reclaimable = max(0, int(stat.get('inactive_file', 0)) +
                              int(stat.get('active_file', 0)) -
                              int(stat.get('file_dirty', 0)) -
                              int(stat.get('file_writeback', 0)))
            headroom = max(0, min(int(maximum),
                                 int(maximum) - int(current) + reclaimable))
            available = min(available, headroom) if available is not None else headroom
    return available


def cores():
    if platform.system() == 'Darwin':
        count = command('sysctl', '-n', 'hw.physicalcpu').strip()
        return max(1, int(count)) if count.isdecimal() else 1
    try:
        affinity = os.sched_getaffinity(0)
    except (AttributeError, OSError):
        affinity = None
    physical = set()
    for line in command('lscpu', '-p=CPU,Core,Socket').splitlines():
        fields = line.strip().split(',')
        if len(fields) != 3 or not all(field.isdecimal() for field in fields):
            continue
        cpu, core, socket = map(int, fields)
        if affinity is None or cpu in affinity:
            physical.add((core, socket))
    # Filter logical CPUs before deduplicating their physical cores: an
    # affinity mask can contain several threads of the same core.
    fallback = len(affinity) if affinity is not None else os.cpu_count()
    count = len(physical) or fallback or 1
    for group in cgroup_paths():
        quota = read(group / 'cpu.max').split()
        if len(quota) == 2 and all(s.isdecimal() for s in quota) and int(quota[1]):
            count = min(count, max(1, int(quota[0]) // int(quota[1])))
    return max(1, count)


def jobs(available, budget_gib, core_cap):
    if budget_gib <= 0:
        raise ValueError('the per-worker memory budget must be positive')
    if available is None:
        return 1
    return max(1, min(core_cap, int((available / GIB - 2) / budget_gib)))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cores', action='store_true')
    ap.add_argument('--rss-gib', type=float, default=4)
    ap.add_argument('--core-cap', type=int)
    args = ap.parse_args()
    count = cores()
    if args.core_cap is not None:
        count = max(1, min(count, args.core_cap))
    print(count if args.cores else jobs(available_memory(), args.rss_gib, count))
