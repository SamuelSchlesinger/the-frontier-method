# Mixed-Hessian frontier theorem and determinant demand

The scalar mixed-Hessian route is now proved for actual compiled polynomial circuits
in `Frontier/Arithmetic`, and included in the paper. It allows arbitrary fields,
arbitrary polynomial gate operations, shared intermediate values, and free constants.
The cut theorem itself needs no fan-in bound. The gate-count transfer uses fan-in two
and one scalar output, whose compiled graph is connected.

The proof uses compiler uniqueness as well as splicing. The two input sides' boundary
differentials have disjoint images; this does not follow merely from disjoint input
coordinates. Evaluation in two independent dual-number directions then makes the
mixed Hessian vanish on the product of their kernels. A finite-dimensional rank lemma
completes the cut bound. The input-order demand is independent of the circuit and
allows its evaluation point to depend on the ordering and prefix.

Sources and scope:

- Harold Abelson, *Lower Bounds on Information Transfer in Distributed Computations*,
  MIT-LCS-TM-102 (April 1978), [MIT repository](https://hdl.handle.net/1721.1/148930).
  This supplies the historical derivative/communication context. The Lean proof uses
  no imported communication lower bound.
- The user-supplied, undated working note *The Frontier Method: Three Lower-Bound Chains*,
  `~/Downloads/frontier_method_three_chains.pdf`, suggested the scalar-Hessian route.
  The source lists no author. SHA-256:
  `d94a9769ed046196c57ad2229d939eeaf0e91d6e3d9868c186b50beebf365d9a`.
- The note's permutation-matching argument for determinant demand is now fully proved
  and formalized. `DeterminantMatching.exists_crossing` gives
  `|S| |Sᶜ| ≤ n² crossing(S,π) + 2n³` for some permutation, for every entry partition.
  `hessian_determinant_permutation` identifies the actual formal Hessian matching;
  `crossing_le_mixedRank` extracts a diagonal submatrix with nonzero entries.
- `hessianDemand_determinant` proves demand `n²/4 - 3n` for every input ordering over
  every field, including characteristic two. The permutation evaluation depends on
  the partition. `lowerBound_determinant_gaussian` proves more than
  `(1.8906244197… - ε) n²` positive-arity gates for sufficiently large `n`, uniformly
  over fields and fan-in-two polynomial bases. All entries' formal occurrence is
  also proved, in `mem_vars_determinant`, for `n ≥ 2`.
- The polynomial-multiplication application and the determinant-width upper bound
  in the note remain unformalized. No smaller cubic layout constant or literature
  priority is asserted.

The paper and Lean theorem concern formal polynomial computation. Equality only as
functions on a finite field does not suffice to identify their formal derivatives.
Every input variable must occur formally in the scalar output for the gate-count
corollary; `upstream_of_mem_vars` verifies that this forces all inputs to be read.

Verification: `lake build --wfail` and `lake env lean scripts/Audit.lean`.
