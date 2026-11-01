"""Check research accounting boundaries independently of native search."""
import base64
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import zlib

from check_campaign import ROOT, sha, unpack
from instruction_residual import residual


class InstructionResidualTests(unittest.TestCase):
    baseline = ROOT / 'research/instruction-baseline.json'

    def changed(self, change):
        data = json.loads(self.baseline.read_text())
        change(data)
        (ROOT / 'build').mkdir(exist_ok=True)
        with tempfile.TemporaryDirectory(dir=ROOT / 'build') as temp:
            path = Path(temp) / 'baseline.json'
            path.write_text(json.dumps(data))
            return residual(path, sha(path))

    def test_frozen_resumption_inventory(self):
        machines, _ = residual(self.baseline, sha(self.baseline))
        self.assertEqual(len(machines), 28653)
        self.assertIn('1LB2LA1RA2RB_2RB3LB0LB1LA', machines)
        self.assertIn('1LB2LB1RB1RA_1RB3LA3RA2LB', machines)

    def test_changed_artifact_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'baseline differs'):
            residual(self.baseline, '0' * 64)

    def test_wrong_count_is_rejected_even_with_fresh_file_hash(self):
        with self.assertRaisesRegex(ValueError, 'Incomplete'):
            self.changed(lambda data: data.update(inventory_rows=28652))

    def test_valid_table_outside_cohort_is_rejected(self):
        def change(data):
            raw = json.dumps(dict(rows=[0])).encode()
            text = unpack(0, 17) + '\n'
            data.update(inventory_rows=1, data=base64.b64encode(zlib.compress(raw)).decode(),
                        uncompressed_sha256=hashlib.sha256(raw).hexdigest(),
                        machine_text_sha256=hashlib.sha256(text.encode()).hexdigest())
        with self.assertRaisesRegex(ValueError, 'outside'):
            self.changed(change)


if __name__ == '__main__':
    unittest.main()
