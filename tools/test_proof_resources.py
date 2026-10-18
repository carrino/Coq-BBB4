import unittest
from unittest.mock import patch

import proof_resources as r


class ResourcesTests(unittest.TestCase):
    def test_mac_page_size_and_reclaimable_pages(self):
        text = '''Mach Virtual Memory Statistics: (page size of 16384 bytes)
Pages free:                              100000.
Pages active:                           1500000.
Pages inactive:                          500000.
Pages speculative:                       200000.
Pages wired down:                        100000.
Pages occupied by compressor:            100000.
'''
        self.assertEqual(r.mac_available(text), 800000 * 16384)
        self.assertIsNone(r.mac_available(text.replace('Pages inactive:', 'Missing:')))

    def test_32_gib_machine_and_low_memory(self):
        self.assertEqual(r.jobs(30 * r.GIB, 6, 8), 4)
        self.assertEqual(r.jobs(30 * r.GIB, 4, 8), 7)
        self.assertEqual(r.jobs(30 * r.GIB, 3, 8), 8)
        self.assertEqual(r.jobs(r.GIB, 4, 8), 1)
        self.assertEqual(r.jobs(None, 4, 8), 1)
        with self.assertRaises(ValueError):
            r.jobs(30 * r.GIB, 0, 8)

    def test_mac_physical_cores(self):
        with patch.object(r.platform, 'system', return_value='Darwin'), \
                patch.object(r, 'command', return_value='8\n'):
            self.assertEqual(r.cores(), 8)

    def test_linux_nested_container_limits(self):
        files = {
            '/proc/self/cgroup': '0::/parent/child',
            '/proc/meminfo': f'MemAvailable: {128 * 1024 ** 2} kB',
            '/sys/fs/cgroup/parent/child/memory.max': 'max',
            '/sys/fs/cgroup/parent/memory.max': str(16 * r.GIB),
            '/sys/fs/cgroup/parent/memory.current': str(3 * r.GIB),
            '/sys/fs/cgroup/parent/cpu.max': '400000 100000',
        }
        with patch.object(r.platform, 'system', return_value='Linux'), \
                patch.object(r, 'read', side_effect=lambda p: files.get(str(p), '')), \
                patch.object(r, 'command', return_value='# CPU,Core,Socket\n' +
                             '\n'.join(f'{i},{i % 32},0' for i in range(64))), \
                patch.object(r.os, 'sched_getaffinity', return_value=set(range(64)), create=True):
            self.assertEqual(r.available_memory(), 13 * r.GIB)
            self.assertEqual(r.cores(), 4)
            self.assertEqual(r.jobs(r.available_memory(), 4, r.cores()), 2)

    def test_linux_affinity_restricted_to_sibling_threads(self):
        topology = '# CPU,Core,Socket\n0,0,0\n1,1,0\n8,0,0\n9,1,0\n'
        with patch.object(r.platform, 'system', return_value='Linux'), \
                patch.object(r, 'command', return_value=topology), \
                patch.object(r, 'read', return_value=''), \
                patch.object(r.os, 'sched_getaffinity', return_value={0, 8}, create=True):
            self.assertEqual(r.cores(), 1)

    def test_linux_core_detection_fallbacks(self):
        with patch.object(r.platform, 'system', return_value='Linux'), \
                patch.object(r, 'command', return_value='unavailable topology'), \
                patch.object(r, 'read', return_value=''), \
                patch.object(r.os, 'cpu_count', return_value=16), \
                patch.object(r.os, 'sched_getaffinity', return_value={2, 3}, create=True) as affinity:
            self.assertEqual(r.cores(), 2)
            affinity.side_effect = OSError('affinity unavailable')
            self.assertEqual(r.cores(), 16)

    def test_container_file_cache_is_reclaimable(self):
        files = {
            '/proc/self/cgroup': '0::/',
            '/proc/meminfo': f'MemAvailable: {30 * 1024 ** 2} kB',
            '/sys/fs/cgroup/memory.max': str(16 * r.GIB),
            '/sys/fs/cgroup/memory.current': str(8 * r.GIB),
            '/sys/fs/cgroup/memory.stat': f'inactive_file {6 * r.GIB}\nanon {2 * r.GIB}',
        }
        with patch.object(r.platform, 'system', return_value='Linux'), \
                patch.object(r, 'read', side_effect=lambda p: files.get(str(p), '')):
            self.assertEqual(r.available_memory(), 14 * r.GIB)
            self.assertEqual(r.jobs(r.available_memory(), 3, 4), 4)
            files['/sys/fs/cgroup/memory.stat'] += (
                f'\nactive_file {r.GIB}\nfile_dirty {r.GIB // 2}')
            self.assertEqual(r.available_memory(), 14 * r.GIB + r.GIB // 2)
            # Host-wide pressure still caps the reclaimable container budget.
            files['/proc/meminfo'] = f'MemAvailable: {2 * 1024 ** 2} kB'
            self.assertEqual(r.available_memory(), 2 * r.GIB)


if __name__ == '__main__':
    unittest.main()
