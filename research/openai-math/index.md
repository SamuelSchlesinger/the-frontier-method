# Synthesis with the OpenAI mathematics collection

Start with the [research conclusions](synthesis.md). The best connection is
conditional accounting for complete transitions, combined with globally valid
boundary descriptions. This investigation adds a checked compatibility lemma
and concrete transfer tests. It does **not** establish a stronger unrestricted
circuit coefficient.

## Download and provenance

The requested repository was downloaded to `external/openai-math/` as a complete
working tree in a shallow Git clone. Snapshot:
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, retrieved 2026-10-06.
The downloaded tree has 722 manuscript directories, 372 catalogue families,
132,851 tracked files, and 122,140 Lean source files. Its Apache-2.0 license and
individual manuscript citation instructions are retained in the checkout.
The clone is ignored by the parent repository. [oai-release][oai-release]

Our comparison baseline is
`f8e6d32df24a7a42930edd921b7e896b6b8cc4aa`. The [source inventory](data/snapshot.json)
records provenance and selected-file hashes. The [bibliography](sources.md)
credits OpenAI's manuscripts and their relevant antecedents, including Courtade,
Kumar, Chen, Gohari, Nair, Anantharam, Bogdanov, Chakrabarti, Jayram, Harvey,
and Wood. Existing Frontier results and Sam McGuire's weighted peeling argument
are distinguished from additions made here.

## What is new here

- **Lean deduction:** two upper potentials on the same prefix states, masses,
  and parent map are closed under pointwise minimum. The new
  `Communication.rootPotential_min_step` and `rootPotential_min_le` are in
  [Communication.lean](../../Frontier/Boundary/Communication.lean), with an exact
  standard-axiom guard in [Audit.lean](../../scripts/Audit.lean).
- **Transfer obstructions:** linear thinning of fractional moments is false;
  one independent median pass cannot rescue the critical Ising mean-cut proxy;
  through-only two-way summaries lose return behavior; linear dirty replay
  fails for a two-AND-gate circuit despite restoring its scratch.
- **Integrated finite diagnostic:** the same four circuits are checked for
  complete-transition support/moment costs and paid single-input restriction
  savings. All 54 restrictions are compared with full truth tables.
- **Precise research targets:** compatible conditional certificates, a
  context-stable description compiler, and a joint-merge layout bound. Each
  branch identifies the missing quantitative theorem and a falsification test.

Minimum closure acts inside the encoding-prefix tree of **one whole graph
transition**. It does not connect separately optimized graph cuts or permit
switching between incompatible layouts. It initially supplies only the smaller
of the existing root budgets. No upstream theorem was needed for its proof.

## The three connections

1. [Information and transition capacity](capacity/index.md): family 119's
   common-output payment, the difference between Shannon/Hellinger information
   and fractional moments, and bounded comparisons with families 140 and 229.
2. [Graph layouts and coherent decompositions](structure/index.md): families
   236 and 174, exact Ising/median calculations, thin-tree congestion failures,
   and screens of 089, 102, 178, 175, and 176.
3. [Circuit models and formal transfer](models/index.md): globally valid
   scheduling descriptions (124), two-way return diagrams (129), affine dirty
   replay (130), and screens of depth-three (112), depth-five (135), and
   one-tape space simulation (137).

The target throughout is unrestricted fan-in-two Boolean DAGs, counting all
positive-arity gates, with free constants and arbitrary fanout. For the existing
hard families, the current coefficient remains
`L = 1 + 1/A = 4.562497678925...`, where
`A = (3/pi) acos((1+2sqrt(2))/4) = 0.280701937272...`.
A universal compatible supply bound with `B<A` is still required to improve it.

## Supplementary Code

The scripts use the Python standard library. Their headers state the claims
they check, and recorded outputs are compared by the aggregate validator.

- [Compatible-potential checks](data/check_potentials.py), [output](data/potentials.json).
- [Same-circuit restriction/capacity probe](data/joint_probe.py), [output](data/joint-probe.json).
- [Common-output and conditioning checks](capacity/data/check_transfer.py), [output](capacity/data/expected.txt).
- [Graph transfer checks](structure/data/check_structure.py), [output](structure/data/expected.txt).
- [Two-way composition and dirty replay](models/data/check_model_transfers.py), [output](models/data/check_model_transfers.expected.txt).
- [Source snapshot verifier](data/snapshot.py), [manifest](data/snapshot.json).
- [Aggregate artifact and citation validator](data/validate.py).

From the repository root:

```sh
python3 research/openai-math/data/validate.py --snapshot
lake build --wfail
lake env lean scripts/Audit.lean
```

Omit `--snapshot` to validate the corpus without the large external clone.
The same-circuit probe intentionally reuses the existing compiler and normalizer;
its independent correctness oracle is exhaustive evaluation of the original
circuits. The [validation record](data/validation.md) states what was actually run.

## Known Limitations

This is a targeted synthesis, not a review of all 722 manuscripts. Upstream
Lean declarations, selected definitions, and Comparator configurations were read
but not rebuilt, compared, or axiom-audited. Comparator challenge files contain
intentional `sorry` target statements; their OAI solution files are separate.
Upstream pins Lean `v4.34.1`; Frontier pins `v4.35.0-rc3`, with different Mathlib
revisions. The external repository has not been added as a Lake dependency.

Formal scope differs from some catalogue headlines: family 229's selected
statements cover supercritical three-state reconstruction, and family 130's
selected Fourier theorem is subsequential. The family-119 scope does not name
its separate Hellinger manuscript. The source-specific documents give details.

The new minimum lemma is checked; the other new deductions have paper arguments
and finite checks. No new universal initial-potential, layout, restriction
coverage, #SAT runtime, or unrestricted circuit lower bound is claimed. The
finite examples are easy control functions, not members of the hard target family.
Repository sources are commit-pinned; no independent web-archive snapshot was obtained.

[oai-release]: sources.md#oai-release
