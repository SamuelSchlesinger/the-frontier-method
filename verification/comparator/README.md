# Comparator proof verification

This harness uses [Lean Comparator](https://github.com/leanprover/comparator) to check the
formalization against the immutable source commit in [`policy.json`](policy.json). It checks
every public theorem defined by a `Frontier` module, including our lemmas in the CSLib
namespace. It does not select a small list of headline results.

For each theorem, Comparator checks its exact statement and the definitions used in that
statement, rejects proof dependencies on unpermitted axioms, and replays the exported
declarations through Lean's kernel. Private and generated theorem proofs are included even
when no public result uses them; their statements may change during refactoring.
The permitted axioms are exactly `propext`, `Quot.sound`,
and `Classical.choice`. There are no definition holes. New or removed public theorems fail
the coverage check, requiring an explicit review of the reference update.

## Run

Requirements: Python 3.11 or later, Git history containing the reference commit, a non-root
account, and Docker with a running Linux engine. Both Apple Silicon and x86-64 hosts use the
pinned Ubuntu image and Lean toolchain. The first run builds a tool image and downloads
the pinned Mathlib cache; allow approximately 15 GB of free disk space, plus exported terms.

```sh
python3 scripts/comparator.py self-test
python3 scripts/comparator.py check
```

Each invocation prints a directory under `.lake/comparator/` containing its logs and JSON
report. A full check records the complete theorem list, source and export SHA-256 hashes,
the reference commit, immutable Docker image ID, verified tool revisions, and checker exit
status. A failed command
returns nonzero and leaves `accepted: false`. A missing tool, failed build, timeout, changed
coverage, or incomplete checker output is a failure, never a skipped or successful check.

The self-test exercises the actual export and Comparator path. It accepts a different proof
of the same statement, and must reject weakened statements, changed definitions, forbidden
axioms, `sorry` in public or unused private proofs, missing or unregistered theorems, an
invalid exported proof term, a weakened axiom policy, definition holes, incomplete proof
inventories, an empty selection, and source or dependency mutation. It also checks that
candidate build caches are excluded and source symlinks rejected.

Use `--candidate /path/to/checkout` to check another source tree. Its Lake configuration,
dependency manifest, and toolchain must match the reference. `--report /path/report.json`
selects the report location; `--timeout SECONDS` bounds each container stage. A timeout
terminates the container created for that stage.

## Isolation and trusted inputs

1. The harness reads reference sources from the pinned Git object. It copies candidate
   `.lean` sources into a fresh project, excluding candidate `.lake` state. The generated
   `VerificationAll` module imports every library source in each snapshot.
2. Only the trusted reference preparation may access the network or build the shared
   dependency cache. Its source hashes are checked before cache reuse. The cache is keyed
   by the reference commit and never writable by candidate containers.
3. Candidate compilation and export run as an unprivileged UID in separate containers with
   no network, a read-only root and source tree, no capabilities, and no host sockets or
   home directory. Only the candidate's fresh `.lake` and temporary directory are writable.
   Reference source files are not mounted. Dependencies are mounted read-only.
4. The checker runs in another container. It imports the pinned Comparator implementation
   and parses the two text exports; it imports no candidate `.olean`. The small
   [`Replay.lean`](Replay.lean) adapter calls upstream `Comparator.verifyMatch`, including
   its statement/definition comparison, axiom check, and kernel replay.

Upstream's CLI expects two modules in one project. Our reference and candidate have the same
module and declaration names in separate projects, so the harness replaces the build/export
orchestration and uses separate Docker containers in place of Landrun. The checking logic is
upstream code. `Main.lean` is copied unchanged to `Comparator/Driver.lean` in the image to
avoid its name collision with the exporter's own `Main` module.

The trust boundary includes this harness and policy, the reference specification, the
pinned compiler/checker/exporter and dependency sources/cache, Docker, the operating system,
and hardware. The code reviewing or invoking the harness must itself be trusted. Changing
the policy or checker in a pull request requires review; a job executing an attacker-edited
harness cannot authenticate that harness. No claim is made that Comparator proves the
informal mathematics, the truth of external extractor hypotheses, or the absence of kernel
or operating-system bugs.

## Updating the reference

A proof refactor that preserves the elaborated public statements and their definitions
should pass without changing the reference. A deliberate API or definition change may be
mathematically sound but will require a new reviewed reference. Keep the theorem hypotheses,
model, and quantifier order visible when reviewing such changes; see the
[formalization guide](../../docs/FORMALIZATION.md).

First review and commit the intended specification and proofs. Then change the full
`reference_revision` in `policy.json` to that commit, run both commands above, and inspect
the report's coverage and results. Never generate the reference from the candidate as part
of the verification command. Reference updates and a new theorem proof should remain
distinguishable in review.

The frozen reference includes the randomized extension and the bridge
`RectangleBias.rectangleFree`, which requires `0 < K` and bias strictly below one.
Before adding that public theorem, Comparator checked the Gaussian and ledger proof
refactors against all 915 public statements of the preceding reference, `24fdc18`.
Earlier published commits remain available in Git; they are not silently used as
specifications for new results.

## Related checks

Keep `lake build --wfail` and `lake env lean scripts/Audit.lean` as fast development checks.
The existing Python experiments check finite examples. Comparator supplies the separate
statement-preservation and proof-replay gate. The CI job runs the adversarial suite before
checking the full library and uploads reports and diagnostic logs.

Comparator is developed by Lean FRO and contributors; its source credits Henrik Böving.
The adapter reuses their implementation rather than implementing a second proof checker.
