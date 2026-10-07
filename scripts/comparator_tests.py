"""Adversarial end-to-end checks of the real Comparator acceptance path."""

from __future__ import annotations

import json
from pathlib import Path
import shutil

from comparator import (AXIOMS, Docker, HARNESS, Rejected, compare, configure_project,
                        copy_sources, export, inventory, source_paths, write_json)


REFERENCE = """import Lean
namespace Frontier
def predicate (n : Nat) : Prop := n = 0
theorem claim : predicate 0 := rfl
theorem reflexive (n : Nat) : n = n := rfl
end Frontier
"""


def fixture(directory: Path, code: str) -> Path:
    directory.mkdir(parents=True)
    (directory / "Frontier.lean").write_text(code)
    (directory / "lakefile.toml").write_text(
        'name = "ComparatorFixture"\n[[lean_lib]]\nname = "Frontier"\n')
    write_json(directory / "lake-manifest.json", {
        "version": "1.3.0", "packagesDir": ".lake/packages", "packages": [],
        "name": "ComparatorFixture", "lakeDir": ".lake", "fixedToolchain": False,
    })
    (directory / "lean-toolchain").write_text(
        json.loads((HARNESS / "policy.json").read_text())["lean_toolchain"] + "\n")
    configure_project(directory, source_paths(directory))
    return directory


def self_test(docker: Docker, directory: Path) -> dict:
    reference = fixture(directory / "reference", REFERENCE)
    docker.run(["lake", "build", "VerificationAll"], project=reference,
               output=directory / "reference-build.log")
    names = inventory(docker, reference, None, directory / "inventory.log").public
    if names != ["Frontier.claim", "Frontier.reflexive"]:
        raise Rejected(f"Unexpected test inventory: {names}")
    export(docker, reference, names, None, directory / "reference.ndjson")
    outcomes = []

    def trial(label: str, code: str, expected: str | None = None) -> Path:
        case = directory / label
        candidate = fixture(case / "candidate", code)
        shutil.copyfile(directory / "reference.ndjson", case / "reference.ndjson")
        try:
            compare(docker, reference, candidate, case, names, reference / ".lake" / "packages")
        except Rejected as error:
            if expected is None or expected.lower() not in str(error).lower():
                raise Rejected(f"{label}: unexpected failure: {error}") from error
        else:
            if expected is not None:
                raise Rejected(f"{label}: an invalid candidate was accepted")
        outcomes.append({"case": label, "expected": "accept" if expected is None else "reject",
                         "passed": True})
        print(f"Self-test passed: {label}", flush=True)
        return case

    good = trial("valid-proof-refactor", REFERENCE.replace(
        "theorem claim : predicate 0 := rfl",
        "private theorem helper : predicate 0 := rfl\ntheorem claim : predicate 0 := helper"))
    trial("weakened-statement", REFERENCE.replace(
        "theorem claim : predicate 0 := rfl", "theorem claim : True := True.intro"),
        "theorem statement do not match")
    trial("changed-definition", REFERENCE.replace(
        "def predicate (n : Nat) : Prop := n = 0", "def predicate (n : Nat) : Prop := True"
    ).replace("theorem claim : predicate 0 := rfl", "theorem claim : predicate 0 := True.intro"),
        "Const does not match")
    trial("forbidden-axiom", REFERENCE.replace(
        "theorem claim : predicate 0 := rfl",
        "axiom forged : predicate 0\ntheorem claim : predicate 0 := forged"), "Illegal axiom")
    trial("sorry-proof", REFERENCE.replace(
        "theorem claim : predicate 0 := rfl", "theorem claim : predicate 0 := by sorry"),
        "Illegal axiom")
    trial("unused-private-sorry", REFERENCE.replace(
        "end Frontier", "private theorem unused : False := by sorry\nend Frontier"),
        "Illegal axiom")
    trial("missing-theorem", REFERENCE.replace("theorem claim : predicate 0 := rfl\n", ""),
          "Public theorem coverage changed")
    trial("unregistered-theorem", REFERENCE.replace(
        "end Frontier", "theorem extra : True := True.intro\nend Frontier"),
        "Public theorem coverage changed")
    trial("source-write-attempt", REFERENCE.replace(
        "namespace Frontier",
        'initialize IO.FS.writeFile "/work/Frontier.lean" "tampered"\nnamespace Frontier'),
        "read-only file system")
    trial("dependency-write-attempt", REFERENCE.replace(
        "namespace Frontier",
        'initialize IO.FS.writeFile "/work/.lake/packages/probe" "tampered"\nnamespace Frontier'),
        "read-only file system")

    def replay_rejection(label: str, expected: str, mutate) -> None:
        case = directory / label
        case.mkdir()
        for name in ("reference.ndjson", "candidate.ndjson", "config.json", "candidate_roots.json"):
            shutil.copyfile(good / name, case / name)
        mutate(case)
        try:
            docker.run(["lake", "env", "lean", "Replay.lean"], project=None,
                       job=case, output=case / "comparator.log")
        except Rejected as error:
            if expected not in str(error):
                raise Rejected(f"{label}: wrong rejection: {error}") from error
        else:
            raise Rejected(f"{label}: the checker accepted an invalid export or policy")
        outcomes.append({"case": label, "expected": "reject", "passed": True})
        print(f"Self-test passed: {label}", flush=True)

    def corrupt_proof(case: Path) -> None:
        path = case / "candidate.ndjson"
        records = [json.loads(line) for line in path.read_text().splitlines()]
        name_map = {0: ""}
        changed = False
        for record in records:
            if "in" in record and "str" in record:
                value = record["str"]
                prefix = name_map[value["pre"]]
                name_map[record["in"]] = prefix + ("." if prefix else "") + value["str"]
            elif "in" in record and "num" in record:
                value = record["num"]
                name_map[record["in"]] = name_map[value["pre"]] + "." + str(value["i"])
            if "thm" in record and name_map[record["thm"]["name"]] == "Frontier.claim":
                # Preserve the exact type and every definition, but put a proposition where
                # its proof term belongs. Only kernel replay should reject this candidate.
                record["thm"]["value"] = record["thm"]["type"]
                changed = True
        if not changed:
            raise Rejected("The corruption test failed to locate the target proof")
        path.write_text("".join(json.dumps(record) + "\n" for record in records))

    def change_policy(case: Path, **changes) -> None:
        path = case / "config.json"
        config = json.loads(path.read_text())
        config.update(changes)
        write_json(path, config)

    replay_rejection("invalid-proof-term", "kernel rejects the solution", corrupt_proof)
    replay_rejection("empty-selection", "Refusing an empty theorem selection",
                     lambda case: change_policy(case, theorem_names=[]))
    replay_rejection("weakened-axiom-policy", "permitted axiom policy has changed",
                     lambda case: change_policy(case, permitted_axioms=[*AXIOMS, "Frontier.forged"]))
    replay_rejection("definition-hole", "Definition holes are not permitted",
                     lambda case: change_policy(case, definition_names=["Frontier.predicate"]))
    replay_rejection("incomplete-proof-inventory", "proof inventory omits a public theorem",
                     lambda case: write_json(case / "candidate_roots.json", []))

    source = directory / "copy-input"
    source.mkdir()
    (source / "Frontier.lean").write_text(REFERENCE)
    (source / ".lake").mkdir()
    (source / ".lake" / "Frontier.olean").write_text("untrusted cached object")
    copy_sources(source, directory / "copy-output")
    if (directory / "copy-output" / ".lake").exists():
        raise Rejected("Candidate build state was copied into the judge")
    outcomes.append({"case": "ignore-candidate-cache", "expected": "exclude", "passed": True})
    (source / "Frontier.lean").unlink()
    (source / "Frontier.lean").symlink_to(reference / "Frontier.lean")
    try:
        copy_sources(source, directory / "symlink-output")
    except Rejected:
        outcomes.append({"case": "reject-source-symlink", "expected": "reject", "passed": True})
    else:
        raise Rejected("A symlinked source was accepted")
    return {"cases": outcomes, "case_count": len(outcomes)}
