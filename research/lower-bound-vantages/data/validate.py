#!/usr/bin/env python3
"""Validates: corpus citations/links resolve and finite checks match recorded output.

Uses only the Python standard library. It does not verify general theorems,
external URL availability, source attribution, or asymptotic constants.
"""

from pathlib import Path
from urllib.parse import unquote, urlsplit
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
CHECKS = (
    ("data/check_layout_identity.py", "data/layout-output.json"),
    ("combinatorial/data/check_claims.py", "combinatorial/data/expected.txt"),
    ("communication/data/check_semantic_quotients.py", "communication/data/expected.txt"),
    ("algebraic/data/check_bridges.py", "algebraic/data/expected.txt"),
    ("structural/data/check_propagation.py", "structural/data/expected.txt"),
)


def prose(text):
    """Exclude fenced code and inline code from prose/link validation."""
    fence = None
    for line in text.splitlines():
        match = re.match(r"^\s{0,3}(`{3,}|~{3,})", line)
        if match:
            token = match.group(1)
            if fence is None:
                fence = token
            elif token[0] == fence[0] and len(token) >= len(fence):
                fence = None
            continue
        if fence is None:
            yield re.sub(r"(`+)(.*?)\1", "", line)


def anchors(text):
    found = set(re.findall(r'<a\s+id="([^"]+)"', text))
    for line in prose(text):
        match = re.match(r"^#{1,6}\s+(.+)", line)
        if match:
            title = re.sub(r"[^\w\- ]", "", match.group(1).lower())
            found.add(title.replace(" ", "-"))
    return found


def check_documents():
    docs = {p: p.read_text() for p in ROOT.rglob("*.md")}
    sources = ROOT / "sources.md"
    keys = set(re.findall(r'<a id="([a-z0-9-]+)"></a>', docs[sources]))
    assert len(keys) == len(re.findall(r'<a id=', docs[sources]))
    used = set()
    graph = {p: set() for p in docs}
    errors = []

    def check_link(p, destination):
        dest = destination.strip("<>")
        parts = urlsplit(dest)
        if parts.scheme or parts.netloc:
            return
        target = (p.parent / unquote(parts.path)).resolve() if parts.path else p
        if not target.exists():
            errors.append(f"{p.relative_to(ROOT)}: missing {dest}")
            return
        if target in docs:
            graph[p].add(target)
            if parts.fragment and unquote(parts.fragment) not in anchors(docs[target]):
                errors.append(f"{p.relative_to(ROOT)}: missing anchor {dest}")

    for p, body in docs.items():
        lines = list(prose(body))
        definitions = {}
        for line in lines:
            match = re.match(r"^\[([a-z0-9-]+)\]:\s+(\S+)\s*$", line)
            if match:
                key, dest = match.groups()
                if key in definitions:
                    errors.append(f"{p.relative_to(ROOT)}: repeated definition {key}")
                definitions[key] = dest
                check_link(p, dest)
        local_used = set()
        for line in lines:
            for display, key in re.findall(r"\[([^\]\n]+)\]\[([a-z0-9-]+)\]", line):
                used.add(key)
                local_used.add(key)
                if display != key:
                    errors.append(f"{p.relative_to(ROOT)}: citation display drift {display}/{key}")
                if key not in keys or key not in definitions:
                    errors.append(f"{p.relative_to(ROOT)}: undefined citation {key}")
                elif (p.parent / definitions[key].split('#')[0]).resolve() != sources:
                    errors.append(f"{p.relative_to(ROOT)}: citation not in master {key}")
            for dest in re.findall(r"(?<!!)\[[^\]\n]*\]\(([^)\n]+)\)", line):
                check_link(p, dest)
        for key in definitions.keys() - local_used:
            errors.append(f"{p.relative_to(ROOT)}: unused definition {key}")
    for key in keys - used:
        errors.append(f"sources.md: unused anchor {key}")
    seen = set()
    pending = [ROOT / "index.md"]
    while pending:
        p = pending.pop()
        if p not in seen:
            seen.add(p)
            pending.extend(graph[p] - seen)
    for p in docs.keys() - seen:
        errors.append(f"orphan document {p.relative_to(ROOT)}")
    if errors:
        raise AssertionError("\n".join(errors))
    print(f"PASS: {len(docs)} Markdown documents; {len(keys)} canonical sources; citations and local links.")


def check_artifacts():
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    for script, expected in CHECKS:
        result = subprocess.run(
            [sys.executable, str(ROOT / script)],
            cwd=ROOT,
            env=env,
            text=True,
            capture_output=True,
            check=True,
        )
        if result.stderr:
            raise AssertionError(f"{script}: unexpected stderr:\n{result.stderr}")
        recorded = (ROOT / expected).read_text()
        if result.stdout != recorded:
            raise AssertionError(f"{script}: output differs from {expected}\n{result.stdout}")
        print(f"PASS: {script} matches {expected}")


if __name__ == "__main__":
    check_documents()
    check_artifacts()
