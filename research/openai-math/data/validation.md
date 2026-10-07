# Validation record

[Index](../index.md) · [Sources](../sources.md)

Run date: 2026-10-06. Upstream snapshot:
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. This record distinguishes checks run
in this repository from upstream declarations inspected as source.

## Local Lean verification

- `lake env lean Frontier/Boundary/Communication.lean` passed.
- `lake build --wfail` passed (3,910 jobs, including cached dependencies).
- `lake env lean scripts/Audit.lean` passed. Its new exact axiom guard for
  `rootPotential_min_le` allows only `propext`, `Classical.choice`, and `Quot.sound`.

The new proofs import no OAI modules. No upstream Lean build or Comparator run
was performed. Upstream configuration and source inspection are not reported as
kernel verification.

## Finite and provenance checks

`python3 research/openai-math/data/validate.py --snapshot` reruns all five corpus
experiments, compares their outputs to the recorded files, validates local links
and canonical citation keys, and checks the downloaded snapshot and cited hashes.
The [manifest](snapshot.json) records exactly which files were hashed.

The existing repository checks also passed:

```sh
python3 scripts/check_algorithms.py
python3 scripts/check_communication.py
python3 research/communication/restrictions.py
python3 research/communication/syndrome_generator.py
python3 research/communication/unambiguous.py
python3 research/communication/rank_profiles.py
```

The new finite checks illustrate or falsify specified transfers. They do not
establish an asymptotic theorem, optimize all layouts, prove minimum circuit
sizes, or validate all claims in the downloaded collection.
