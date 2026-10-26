#!/usr/bin/env python3
"""Check the extracted searcher against a formerly overflowing key case."""
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
with tempfile.TemporaryDirectory() as temp:
    source, residue = Path(temp) / "input", Path(temp) / "residue"
    source.write_text("1LB2LA1RB_0RB2LB1RA\n")
    result = subprocess.run(
        [str(root / "small/build/probe"), "state-rw", str(source), str(residue),
         "2", "3", "59", "67", "3", "67", "512", "2"],
        check=True, capture_output=True, text=True)
    assert "solved=0 total=1" in result.stdout, result.stdout
    assert residue.read_text() == source.read_text()
print("Exact-key extraction regression passed.")
