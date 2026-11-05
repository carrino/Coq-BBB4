"""Cross-check scanner boundaries against a small, independent Python simulator."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

from scan_candidates import canonical


def observed(machine, start, stop):
    cells = [row[j:j+3] for row in machine.split('_') for j in (0, 3)]
    tape = {}
    q = pos = 0
    states, instructions = [None]*4, [None]*8
    for t in range(stop+1):
        a = tape.get(pos, 0)
        k = 2*q+a
        if t >= start:
            if states[q] is None: states[q] = t
            if instructions[k] is None: instructions[k] = t
        if cells[k] == '---': break
        w, dr, nx = cells[k]
        tape[pos] = int(w)
        pos += 1 if dr == 'R' else -1
        q = ord(nx)-65
    return states, instructions


class ScannerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory()
        cls.binary = Path(cls.temp.name)/'scan'
        subprocess.run(['c++', '-O2', '-std=c++17', str(Path(__file__).with_name('scan.cpp')),
                        '-o', str(cls.binary)], check=True)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def run_scan(self, machine, start, cap, mode):
        result = subprocess.run([str(self.binary), str(start), str(cap), mode],
                                input=machine+'\n', text=True, capture_output=True, check=True)
        row = json.loads(result.stdout)
        st, ins = observed(machine, start, row['stopped_at'])
        self.assertEqual(row['state_first'], st)
        self.assertEqual(row['instruction_first'], ins)
        return row

    def test_state_endpoint(self):
        r = self.run_scan('1RB0RB_1LA1LB_------_------', 6, 9, 'state')
        self.assertEqual(r['state_first'], [9, 6, None, None])
        self.assertEqual(r['state_control_closed_at'], 9)

    def test_instruction_endpoint(self):
        r = self.run_scan('1RB0LB_1LA0RA_------_------', 8, 17, 'instruction')
        self.assertEqual(r['instruction_first'][3], 17)
        self.assertEqual(r['instruction_control_closed_at'], 17)

    def test_cap_is_not_silence(self):
        r = self.run_scan('1RB0LB_1LA0RA_------_------', 8, 16, 'instruction')
        self.assertEqual(r['status'], 'cap')
        self.assertIsNone(r['instruction_first'][3])
        self.assertIsNone(r['instruction_control_closed_at'])

    def test_undefined_slot_is_observed(self):
        r = self.run_scan('------_------_------_------', 0, 0, 'instruction')
        self.assertEqual(r['instruction_first'][0], 0)

    def test_never_visited_states_are_not_required(self):
        r = self.run_scan('0RA---_------_------_------', 1, 4, 'state')
        self.assertEqual(r['state_control_closed_at'], 1)
        self.assertEqual(r['state_first'], [1, None, None, None])

    def test_canonical_preserves_first_visit_times(self):
        machine = '1LC0RC_------_1RA0LA_------'
        canon = canonical(machine)
        self.assertEqual(canonical(canon), canon)
        before = sorted(x for x in observed(machine, 8, 30)[0] if x is not None)
        after = sorted(x for x in observed(canon, 8, 30)[0] if x is not None)
        self.assertEqual(before, after)


if __name__ == '__main__':
    unittest.main()
