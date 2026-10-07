#!/usr/bin/env python3
"""Compare all public Frontier theorems with a pinned reference using Lean Comparator.

Candidate Lean code runs only in disposable containers. It cannot see reference sources,
the Docker socket, or the host home directory. Comparator parses text exports and never
imports candidate object files. See verification/comparator/README.md for the trust boundary.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid


ROOT = Path(__file__).resolve().parents[1]
HARNESS = ROOT / "verification" / "comparator"
CACHE = ROOT / ".lake" / "comparator"
IMAGE_TAG = "frontier-comparator:lean4.35.0-rc3"
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
PROJECT_FILES = ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
EXPORTER = "/opt/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
# These are Comparator.primitiveTargets and builtinTargets at the pinned revision.
PRIMITIVES = [
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div", "Nat.mod",
    "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor", "Nat.shiftLeft",
    "Nat.shiftRight", "String.ofList", "Char.ofNat", "List", "eagerReduce", "Nat",
    "String", "String.mk", "Char", "optParam", "autoParam", "semiOutParam", "outParam",
    "Quot", "Quot.mk", "Quot.lift", "Quot.ind",
]


class Rejected(RuntimeError):
    """A failed prerequisite or proof check; never an accepted judgment."""


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write_json(path: Path, data: object) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def command(args: list[str], *, cwd: Path = ROOT, timeout: int = 1800) -> str:
    result = subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    if result.returncode:
        raise Rejected(f"Command failed: {args[0]}\n{result.stderr[-4000:]}{result.stdout[-4000:]}")
    return result.stdout


def source_paths(root: Path) -> list[str]:
    """Select only library sources; reject symlinks, including directory symlinks."""
    result = ["Frontier.lean"]
    library = root / "Frontier"
    if library.is_symlink():
        raise Rejected(f"Symlinked library directory: {library}")
    if library.exists():
        for directory, dirs, files in os.walk(library, followlinks=False):
            for name in [*dirs, *files]:
                path = Path(directory) / name
                if path.is_symlink():
                    raise Rejected(f"Symlink in library source: {path}")
            result.extend(str((Path(directory) / name).relative_to(root))
                          for name in files if name.endswith(".lean"))
    for name in result:
        path = root / name
        if path.is_symlink() or not path.is_file():
            raise Rejected(f"Expected a regular source file: {path}")
        if not all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", part)
                   for part in Path(name).with_suffix("").parts):
            raise Rejected(f"Unsupported Lean module path: {name}")
    return sorted(result)


def hashes(root: Path, names: list[str]) -> dict[str, str]:
    return {name: digest(root / name) for name in names}


def copy_sources(source: Path, destination: Path) -> list[str]:
    names = source_paths(source)
    destination.mkdir(parents=True)
    for name in names:
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / name, target)
    return names


def reference_sources(revision: str, destination: Path) -> list[str]:
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise Rejected("The reference must be a full immutable Git commit ID")
    if command(["git", "--no-replace-objects", "rev-parse", f"{revision}^{{commit}}"],
               timeout=30).strip() != revision:
        raise Rejected("Reference commit identity mismatch")
    entries = command(["git", "--no-replace-objects", "ls-tree", "-r", revision,
                       "--", "Frontier.lean", "Frontier",
                       *PROJECT_FILES], timeout=30)
    destination.mkdir(parents=True)
    for entry in entries.splitlines():
        metadata, name = entry.split("\t", 1)
        if not (name.endswith(".lean") or name in PROJECT_FILES):
            continue
        if metadata.split()[0] not in ("100644", "100755"):
            raise Rejected(f"Non-regular reference source: {name}")
        target = destination / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(subprocess.check_output(
            ["git", "--no-replace-objects", "show", f"{revision}:{name}"], cwd=ROOT))
    return source_paths(destination)


def configure_project(project: Path, names: list[str], reference: Path | None = None) -> None:
    if reference is not None:
        for name in PROJECT_FILES:
            path = reference / name
            if path.exists():
                shutil.copyfile(path, project / name)
    lakefile = project / "lakefile.toml"
    lakefile.write_text(lakefile.read_text() + '\n[[lean_lib]]\nname = "VerificationAll"\n')
    modules = [".".join(Path(name).with_suffix("").parts) for name in names]
    (project / "VerificationAll.lean").write_text("".join(f"import {m}\n" for m in modules))
    (project / ".lake").mkdir()
    (project / ".lake" / "packages").mkdir()


class Docker:
    def __init__(self, image: str, timeout: int):
        self.image = image
        self.timeout = timeout

    @classmethod
    def build(cls, directory: Path, timeout: int) -> Docker:
        print("Building the pinned Comparator image", flush=True)
        log = directory / "image.log"
        # Keep a distinct tag alive for this run, even when another check rebuilds the image.
        tag = IMAGE_TAG + "-" + directory.name
        with log.open("w") as output:
            result = subprocess.run(["docker", "build", "--tag", tag, str(HARNESS)],
                                    stdout=output, stderr=subprocess.STDOUT, timeout=timeout)
        if result.returncode:
            raise Rejected(f"Image build failed; see {log}\n{log.read_text()[-4000:]}")
        image = command(["docker", "image", "inspect", "--format", "{{.Id}}", tag]).strip()
        if not re.fullmatch(r"sha256:[0-9a-f]{64}", image):
            raise Rejected("Docker did not return an immutable image ID")
        return cls(image, timeout)

    def run(self, args: list[str], *, project: Path | None, output: Path,
            packages: Path | None = None, network: bool = False,
            job: Path | None = None) -> None:
        """Every run has a distinct namespace, a read-only root, and a bounded process count."""
        name = "frontier-comparator-" + uuid.uuid4().hex
        cmd = ["docker", "run", "--rm", "--init", "--name", name,
               "--user", f"{os.getuid()}:{os.getgid()}", "--read-only",
               "--cap-drop", "ALL", "--security-opt", "no-new-privileges",
               "--pids-limit", "512", "--network", "bridge" if network else "none",
               "--tmpfs", "/tmp:rw,nosuid,nodev,size=2g",
               "--env", "XDG_CACHE_HOME=/tmp/cache",
               "--mount", f"type=bind,src={HARNESS},dst=/harness,readonly"]
        if project is not None:
            cmd += ["--workdir", "/work",
                    "--mount", f"type=bind,src={project},dst=/work,readonly",
                    "--mount", f"type=bind,src={project / '.lake'},dst=/work/.lake"]
            if packages is not None:
                cmd += ["--mount", f"type=bind,src={packages},dst=/work/.lake/packages,readonly"]
        if job is not None:
            cmd += ["--workdir", "/opt/comparator", "--env", "FRONTIER_COMPARATOR_JOB=/job",
                    "--mount", f"type=bind,src={job},dst=/job,readonly"]
        cmd += [self.image, *args]
        stderr_path = output.with_suffix(output.suffix + ".stderr")
        try:
            with output.open("wb") as stdout, stderr_path.open("wb") as stderr:
                result = subprocess.run(cmd, stdout=stdout, stderr=stderr, timeout=self.timeout)
            if result.returncode:
                raise Rejected(f"Container exited {result.returncode}; see {output}\n"
                               f"{stderr_path.read_text(errors='replace')[-2000:]}\n"
                               f"{output.read_text(errors='replace')[-4000:]}")
        except (subprocess.TimeoutExpired, KeyboardInterrupt):
            subprocess.run(["docker", "rm", "--force", name], capture_output=True, timeout=30)
            raise


@dataclass(frozen=True)
class Inventory:
    public: list[str]
    proofs: list[str]


def inventory(docker: Docker, project: Path, packages: Path | None, log: Path) -> Inventory:
    docker.run(["lake", "env", "lean", "/harness/Inventory.lean"], project=project,
               packages=packages, output=log)
    lines = [line.removeprefix("FRONTIER_THEOREMS=") for line in log.read_text().splitlines()
             if line.startswith("FRONTIER_THEOREMS=")]
    if len(lines) != 1:
        raise Rejected("Missing or ambiguous theorem inventory")
    data = json.loads(lines[0])
    for key in ("public", "proofs"):
        names = data[key]
        if not isinstance(names, list) or not names or any(not isinstance(n, str) for n in names):
            raise Rejected("Invalid or empty theorem inventory")
        if names != sorted(set(names)):
            raise Rejected("The theorem inventory must be sorted and unique")
    if not set(data["public"]).issubset(data["proofs"]):
        raise Rejected("The proof inventory omits a public theorem")
    return Inventory(data["public"], data["proofs"])


def export(docker: Docker, project: Path, names: list[str], packages: Path | None,
           path: Path) -> None:
    targets = list(dict.fromkeys([*names, *AXIOMS, *PRIMITIVES]))
    docker.run(["lake", "env", EXPORTER, "VerificationAll", "--", *targets],
               project=project, packages=packages, output=path)
    if path.stat().st_size == 0:
        raise Rejected("The exporter produced an empty file")


def compare(docker: Docker, reference: Path, candidate: Path, directory: Path,
            names: list[str], packages: Path | None) -> dict:
    before = hashes(candidate, source_paths(candidate) + ["VerificationAll.lean"]
                    + [name for name in PROJECT_FILES if (candidate / name).exists()])
    before_reference = hashes(reference, source_paths(reference) + ["VerificationAll.lean"]
                             + [name for name in PROJECT_FILES if (reference / name).exists()])
    print(f"Building the candidate; comparing {len(names)} public theorems", flush=True)
    docker.run(["lake", "build", "VerificationAll"], project=candidate, packages=packages,
               output=directory / "candidate-build.log")
    actual = inventory(docker, candidate, packages, directory / "candidate-inventory.log")
    if actual.public != names:
        missing = sorted(set(names) - set(actual.public))
        added = sorted(set(actual.public) - set(names))
        raise Rejected(f"Public theorem coverage changed: missing={missing}, added={added}. "
                       "Review new statements before updating the reference.")
    export(docker, candidate, actual.proofs, packages, directory / "candidate.ndjson")
    if hashes(candidate, list(before)) != before:
        raise Rejected("Candidate sources changed during compilation or export")
    if hashes(reference, list(before_reference)) != before_reference:
        raise Rejected("Reference sources changed during candidate compilation or export")
    config = {"challenge_module": "VerificationAll", "solution_module": "VerificationAll",
              "theorem_names": names, "permitted_axioms": AXIOMS}
    write_json(directory / "config.json", config)
    write_json(directory / "candidate_roots.json", actual.proofs)
    print("Comparator: checking statements, definitions, axioms, and kernel replay", flush=True)
    docker.run(["lake", "env", "lean", "Replay.lean"], project=None,
               job=directory, output=directory / "comparator.log")
    marker = f"Comparator accepted {len(names)} theorem statements and proofs."
    if marker not in (directory / "comparator.log").read_text().splitlines():
        raise Rejected("The checker exited without its acceptance record")
    return {"theorem_count": len(names), "theorems": names,
            "proof_root_count": len(actual.proofs), "proof_roots": actual.proofs,
            "candidate_files_sha256": before,
            "reference_export_sha256": digest(directory / "reference.ndjson"),
            "candidate_export_sha256": digest(directory / "candidate.ndjson")}


def prepare_reference(docker: Docker, reference: Path, revision: str, directory: Path) -> Path:
    """Cache only trusted builds; candidates never receive write access to this directory."""
    cache = CACHE / "references" / revision
    cache.parent.mkdir(parents=True, exist_ok=True)
    selected = source_paths(reference) + ["VerificationAll.lean", *PROJECT_FILES]
    expected = hashes(reference, selected)
    with (cache.parent / (revision + ".lock")).open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise Rejected("Another process is preparing this reference cache; retry after it exits") from error
        if cache.exists():
            if cache.is_symlink() or hashes(cache, selected) != expected:
                raise Rejected("The cached reference sources differ from the pinned commit")
        else:
            reference.rename(cache)
        if not (cache / ".dependencies-fetched").exists():
            docker.run(["lake", "exe", "cache", "get"], project=cache,
                       output=directory / "dependencies.log", network=True)
            (cache / ".dependencies-fetched").write_text("Pinned cache download completed.\n")
        docker.run(["lake", "build", "VerificationAll"], project=cache,
                   output=directory / "reference-build.log", network=True)
        if hashes(cache, selected) != expected:
            raise Rejected("Trusted reference compilation changed a source file")
    return cache


def check(docker: Docker, directory: Path, candidate_source: Path) -> dict:
    policy = json.loads((HARNESS / "policy.json").read_text())
    if policy["permitted_axioms"] != AXIOMS:
        raise Rejected("The checked-in axiom policy has changed")
    reference = directory / "reference"
    ref_names = reference_sources(policy["reference_revision"], reference)
    expected_project = hashes(reference, list(PROJECT_FILES))
    for name in PROJECT_FILES:
        path = candidate_source / name
        if path.is_symlink() or not path.is_file() or digest(path) != expected_project[name]:
            raise Rejected(f"The trusted project configuration changed: {name}")
    if (reference / "lean-toolchain").read_text().strip() != policy["lean_toolchain"]:
        raise Rejected("Reference toolchain mismatch")
    reference_hashes = hashes(reference, ref_names + list(PROJECT_FILES))
    candidate = directory / "candidate"
    candidate_names = copy_sources(candidate_source, candidate)
    # Copy the trusted configuration before adding the generated all-module target.
    configure_project(candidate, candidate_names, reference)
    configure_project(reference, ref_names)
    print("Preparing the trusted reference and pinned dependency cache", flush=True)
    reference = prepare_reference(docker, reference, policy["reference_revision"], directory)
    declarations = inventory(docker, reference, None, directory / "reference-inventory.log")
    export(docker, reference, declarations.public, None, directory / "reference.ndjson")
    result = compare(docker, reference, candidate, directory, declarations.public,
                     reference / ".lake" / "packages")
    result.update(reference_revision=policy["reference_revision"],
                  reference_files_sha256=reference_hashes,
                  reference_module_count=len(ref_names), candidate_module_count=len(candidate_names))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["check", "self-test", "image"])
    parser.add_argument("--candidate", type=Path, default=ROOT)
    parser.add_argument("--timeout", type=int, default=1800, help="seconds per container stage")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    CACHE.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix=args.command + "-", dir=CACHE)).resolve()
    report_path = args.report or directory / "report.json"
    result = {"schema_version": 1, "accepted": False, "command": args.command,
              "work_directory": str(directory), "permitted_axioms": AXIOMS,
              "started_at_unix": time.time()}
    print(f"Verification artifacts: {directory}", flush=True)
    try:
        if os.getuid() == 0:
            raise Rejected("Run the harness as a non-root user")
        docker = Docker.build(directory, args.timeout)
        result["image_id"] = docker.image
        docker.run(["python3", "/harness/versions.py"], project=None,
                   output=directory / "versions.json")
        result["tools"] = json.loads((directory / "versions.json").read_text())
        result["harness_sha256"] = {str(p.relative_to(ROOT)): digest(p)
                                   for p in [Path(__file__), *sorted(HARNESS.glob("*"))]
                                   if p.is_file()}
        if args.command == "check":
            result.update(check(docker, directory, args.candidate.resolve()))
        elif args.command == "self-test":
            from comparator_tests import self_test
            result.update(self_test(docker, directory))
        result["passed"] = True
        result["accepted"] = args.command == "check"
        print("PASS", flush=True)
        return 0
    except (Rejected, subprocess.SubprocessError, OSError, ValueError, KeyError) as error:
        result["passed"] = False
        result["error"] = str(error)
        print(f"FAIL: {error}", file=sys.stderr, flush=True)
        return 1
    finally:
        result["completed_at_unix"] = time.time()
        write_json(report_path, result)
        print(f"Report: {report_path}", flush=True)


if __name__ == "__main__":
    sys.modules["comparator"] = sys.modules[__name__]
    raise SystemExit(main())
