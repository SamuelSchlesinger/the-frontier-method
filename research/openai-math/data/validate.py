#!/usr/bin/env python3
"""Validates: every synthesis document/citation resolves and all checks reproduce.

Reuses this repository's existing corpus validator. Pass --snapshot to check the
downloaded upstream revision and cited-file hashes as well. No upstream theorem
is compiled by this command.
"""

import argparse
import importlib.util
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", action="store_true")
    args = parser.parse_args()
    validator = ROOT.parent / "lower-bound-vantages/data/validate.py"
    spec = importlib.util.spec_from_file_location("frontier_corpus_validator", validator)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.ROOT = ROOT
    module.CHECKS = (
        ("data/check_potentials.py", "data/potentials.json"),
        ("data/joint_probe.py", "data/joint-probe.json"),
        ("capacity/data/check_transfer.py", "capacity/data/expected.txt"),
        ("structure/data/check_structure.py", "structure/data/expected.txt"),
        ("models/data/check_model_transfers.py", "models/data/check_model_transfers.expected.txt"),
    )
    module.check_documents()
    module.check_artifacts()
    if args.snapshot:
        subprocess.run([sys.executable, str(ROOT / "data/snapshot.py")], check=True)
    else:
        print("Snapshot hashes not rechecked; use --snapshot with external/openai-math present.")


if __name__ == "__main__":
    main()
