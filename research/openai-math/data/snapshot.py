#!/usr/bin/env python3
"""Validates: the downloaded source snapshot and cited-file hashes match provenance.

Checks repository metadata and files, not the correctness of the upstream proofs.
Run with --write only when deliberately recording a new reviewed snapshot.
"""

from pathlib import Path
from urllib.parse import unquote
import argparse
import hashlib
import json
import re
import subprocess

CORPUS = Path(__file__).resolve().parents[1]
REPO = CORPUS.parents[1]
UPSTREAM = REPO / "external/openai-math"
REV = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
BASELINE = "f8e6d32df24a7a42930edd921b7e896b6b8cc4aa"


def git(*args):
    return subprocess.check_output(["git", "-C", str(UPSTREAM), *args], text=True).strip()


def snapshot():
    assert git("rev-parse", "HEAD") == REV, "upstream revision changed"
    assert not git("status", "--porcelain", "--untracked-files=no"), "upstream tracked files changed"
    files = git("ls-files").splitlines()
    contents = (UPSTREAM / "CONTENTS.md").read_text()
    families = re.findall(r"^\*\*(\d+)\.", contents, re.M)
    assert len(set(families)) == len(families)
    readme = (UPSTREAM / "README.md").read_text()
    advertised = re.search(r"(\d+) manuscripts organized into (\d+) families", readme)
    assert advertised
    manuscripts = sum(p.startswith("preprints/") and p.count("/") == 2 and
                      p.endswith("/README.md") for p in files)
    assert manuscripts == int(advertised[1])
    assert len(families) == int(advertised[2])
    source_text = (CORPUS / "sources.md").read_text()
    cited = set(re.findall(
        rf"https://github\.com/openai/math/blob/{REV}/([^\s)<>]+)", source_text))
    paths = {"README.md", "CONTENTS.md", "LICENSE", "lean/README.md",
             "lean/lean-toolchain", "lean/lakefile.lean", "lean/formalization.yaml",
             "lean/ComparatorChallenges/README.md"} | {unquote(p) for p in cited}
    directories = set(re.findall(
        rf"https://github\.com/openai/math/tree/{REV}/(preprints/[^\s)<>]+)", source_text))
    for directory in directories:
        folder = UPSTREAM / unquote(directory)
        assert folder.is_dir(), directory
        paths.update(str(p.relative_to(UPSTREAM)) for p in folder.rglob("*")
                     if p.is_file() and p.suffix in {".md", ".tex", ".bib"})
    for family in re.findall(r'<a id="oai(\d+)[a-z]*"></a>', source_text):
        scope = f"lean/docs/{family}.md"
        if (UPSTREAM / scope).is_file():
            paths.add(scope)
    hashes = {}
    for path in sorted(paths):
        f = (UPSTREAM / path).resolve()
        assert f.is_relative_to(UPSTREAM.resolve()), path
        assert f.is_file(), path
        hashes[path] = hashlib.sha256(f.read_bytes()).hexdigest()
    return {
        "upstream": "https://github.com/openai/math",
        "revision": REV,
        "downloaded_on": "2026-10-06",
        "clone_depth": 1,
        "frontier_baseline": BASELINE,
        "tracked_files": len(files),
        "lean_source_files": sum(p.endswith(".lean") for p in files),
        "manuscript_directories": manuscripts,
        "result_families": len(families),
        "upstream_toolchain": (UPSTREAM / "lean/lean-toolchain").read_text().strip(),
        "upstream_build_status": "not rebuilt; selected statements and sources inspected",
        "sha256": hashes,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    actual = snapshot()
    destination = CORPUS / "data/snapshot.json"
    if args.write:
        destination.write_text(json.dumps(actual, indent=2, sort_keys=True) + "\n")
    else:
        assert actual == json.loads(destination.read_text()), "snapshot evidence drifted"
    print(f"Snapshot {REV[:12]}: {actual['result_families']} families, "
          f"{actual['manuscript_directories']} manuscripts, "
          f"{len(actual['sha256'])} cited/metadata file hashes verified.")


if __name__ == "__main__":
    main()
