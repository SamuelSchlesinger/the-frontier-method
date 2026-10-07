"""Check the tool image against the declared policy, without importing candidate code."""

import hashlib
import json
from pathlib import Path
import subprocess


policy = json.loads(Path('/harness/policy.json').read_text())
actual = {}
for key, directory in [
    ('comparator_revision', '/opt/comparator'),
    ('lean4export_revision', '/opt/comparator/.lake/packages/lean4export'),
]:
    actual[key] = subprocess.check_output(
        ['git', '-C', directory, 'rev-parse', 'HEAD'], text=True).strip()
    if actual[key] != policy[key]:
        raise SystemExit(f'{key} differs from the pinned policy')
actual['lean_version'] = subprocess.check_output(['lean', '--version'], text=True).strip()
version = policy['lean_toolchain'].split(':v', 1)[1]
if f'version {version},' not in actual['lean_version']:
    raise SystemExit('The compiler differs from the pinned Lean toolchain')
original = Path('/opt/comparator/Main.lean').read_bytes()
driver = Path('/opt/comparator/Comparator/Driver.lean').read_bytes()
if original != driver:
    raise SystemExit('The upstream Comparator driver was modified')
actual['upstream_driver_sha256'] = hashlib.sha256(original).hexdigest()
print(json.dumps(actual, indent=2, sort_keys=True))
