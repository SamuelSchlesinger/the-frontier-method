#!/usr/bin/env python3
"""Validates: all four research computations reproduce their saved outputs.

Also runs citation/link/reachability validation. Does not certify asymptotic gains
or substitute for the literature's proof hypotheses. Standard library only.
"""

from pathlib import Path
import difflib
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
JOBS = (
    ("classical/data/check_classical_deductions.py", "classical/data/check_classical_deductions.txt"),
    ("spectral/data/check_proposals.py", "spectral/data/check_proposals-output.json"),
    ("parameters/data/validate_conversions.py", "parameters/data/validation-output.txt"),
    ("structural/data/check_reductions.py", "structural/data/check_reductions.txt"),
)


def main():
    for script, expected in JOBS:
        actual = subprocess.run([sys.executable, str(ROOT / script)],
                                check=True, text=True, capture_output=True).stdout
        saved = (ROOT / expected).read_text()
        if actual != saved:
            difference = "".join(difflib.unified_diff(
                saved.splitlines(True), actual.splitlines(True),
                fromfile=expected, tofile=script))
            raise SystemExit(difference)
        print(f"PASS: {script}", flush=True)
    subprocess.run([sys.executable, str(ROOT / "data/check_corpus.py")], check=True)


if __name__ == "__main__":
    main()
