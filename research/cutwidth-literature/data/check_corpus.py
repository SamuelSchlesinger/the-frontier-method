#!/usr/bin/env python3
"""Validates: research citations resolve uniquely, local links exist, no orphan Markdown.

This structural check does not verify the mathematical content or external URLs.
Fenced code and inline code are excluded from Markdown citation/link scanning.
"""

from pathlib import Path
import re
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parents[1]


def prose(source):
    result = []
    fence = None
    for line in source.splitlines():
        match = re.match(r"^\s*(`{3,}|~{3,})", line)
        if match:
            marker = match.group(1)
            if fence is None:
                fence = marker[0]
            elif marker[0] == fence:
                fence = None
            continue
        if fence is None:
            result.append(re.sub(r"(`+).*?\1", "", line))
    return "\n".join(result)


def main():
    errors = []
    documents = sorted(ROOT.rglob("*.md"))
    sources = (ROOT / "sources.md").read_text()
    anchors = re.findall(r'<a id="([a-z0-9-]+)"></a>', sources)
    if len(anchors) != len(set(anchors)):
        errors.append("Duplicate source anchor")
    anchors = set(anchors)
    cited = set()
    graph = {path.resolve(): set() for path in documents}
    for path in documents:
        body = prose(path.read_text())
        definitions = dict(re.findall(r"^\[([a-z0-9-]+)\]:\s*(\S+)", body, re.M))
        if "## Local References" in body:
            errors.append(f"Unassembled Local References: {path.relative_to(ROOT)}")
        for display, key in re.findall(r"\[([^\]\n]+)\]\[([a-z0-9-]+)\]", body):
            cited.add(key)
            if display != key:
                errors.append(f"Citation display drift: {path.name}: [{display}][{key}]")
            if key not in anchors:
                errors.append(f"Undefined source key: {path.name}: {key}")
            if key not in definitions:
                errors.append(f"Missing local link definition: {path.name}: {key}")
            elif not definitions[key].endswith(f"sources.md#{key}"):
                errors.append(f"Noncanonical citation definition: {path.name}: {key}")
        links = re.findall(r"\[[^\]\n]*\]\(([^)\n]+)\)", body)
        links.extend(definitions.values())
        for link in links:
            if re.match(r"(?:https?://|mailto:|#)", link):
                continue
            target = unquote(link.split("#", 1)[0].strip("<>"))
            target = re.sub(r":\d+$", "", target)
            resolved = (path.parent / target).resolve()
            if not resolved.exists():
                errors.append(f"Missing local target: {path.relative_to(ROOT)}: {link}")
            if resolved in graph:
                graph[path.resolve()].add(resolved)
    if anchors - cited:
        errors.append(f"Uncited source anchors: {sorted(anchors-cited)}")
    reached = set()
    pending = [(ROOT / "index.md").resolve()]
    while pending:
        path = pending.pop()
        if path in reached:
            continue
        reached.add(path)
        pending.extend(graph.get(path, ()))
    orphans = sorted(str(path.relative_to(ROOT)) for path in graph if path not in reached)
    if orphans:
        errors.append(f"Orphan Markdown documents: {orphans}")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"PASS: {len(documents)} Markdown files, {len(anchors)} unique cited sources;")
    print("zero undefined keys, display drift, unused anchors, missing local links, or orphans.")


if __name__ == "__main__":
    main()
