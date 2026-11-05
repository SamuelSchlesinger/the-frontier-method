# Lower-bound methods viewed through the frontier method

Research comparison started 2026-10-06, against repository baseline `d81d97a`.

Start with the [research conclusions](synthesis.md): the leading direction is a
restriction-or-compression theorem, with exact cumulative accounting and coherent
semantic transitions. The branching route now has a standard target parameter,
line-graph treewidth. None of the comparisons supplies a new unrestricted gate
coefficient. The [bibliography](sources.md) credits the underlying methods.

The companion [extractor–frontier hybrid failure catalogue](../frontier-hybrids/README.md)
records specific unsuccessful implications from the cut, extractor, multi-output,
and computation-segmentation exploration. It includes counterexamples and
distinguishes them from open structural steps.

## Question and scope

Which established lower-bound mechanisms can strengthen the frontier method, rather
than merely redescribe it? The main target is explicit Boolean functions against
unrestricted fan-in-two circuits, counting positive-arity gates, with arbitrary
fan-out and the full binary basis. Arithmetic, linear, formula, branching-program,
depth-restricted, and monotone results are separate models and possible sources of
ideas. This is a systematic comparison of major technique families and their
subfamilies, not a claim to enumerate every historical variant.

## Baseline and obligations

The present unrestricted coefficient is
`L = 1 + 1/A = 4.562497678925021...`, where
`A = (3/pi) acos((1+2sqrt(2))/4) = 0.2807019372716472...`.
Exact threshold charging gives `|S| <= (K-1)^2 D`; graph compilation gives
`beta <= s-n+o(n)` and Gaussian layouts give `log2 D <= A(s-n)+o(n)`.
Five would follow from a sound representation with
`log2 D <= (s-n)/4+o(n)`, or a restriction/terminal composition with the same effect.

Already present, and not to be announced as new outputs of this survey:

- Weighted disjoint peeling (credit Sam McGuire), capped transition masses,
  fractional moments, and conditional information potentials.
- Branching/decomposable demand, higher-fan-in constants, and mixed-fiber demand.
- Distinct-signal capacity, additive generators, affine-prefix syndromes,
  joint boundary/syndrome rank, and graphic cycle formulas.
- Input restriction rules preserving `5d-s`; no global terminal-coverage theorem.

Current supporting notes: [communication](../communication/README.md),
[restrictions](../communication/restrictions.md),
[additive generators](../communication/additive.md), and
[joint rank](../communication/joint.md).

## How to read the comparison

Each family must specify its model, resource, mechanism, the frontier component it
could modify, a concrete transfer lemma or test, and a failure example or missing
hypothesis. Distinguish established literature, deductions proved in this corpus,
finite checks, conjectural bridges, and questions of priority. Novelty is not
assumed.

Every transfer must retain quantitative constants and state its model: Boolean or
arithmetic; single or multiple outputs; DAG or formula; signed or nonnegative;
exact, approximate, nondeterministic, or unambiguous; fixed or adaptive partitions.
An unspecified simulation overhead is insufficient for a better leading constant.
Any rigorously justified coefficient below `A` is useful; `1/4` is a stretch target.

1. [Combinatorial simplification](combinatorial/index.md): gate elimination,
   adaptive restrictions, random projections, switching/shrinkage, Nechiporuk, formula adversaries,
   sensitivity and boundary measures, direct sums and composition.
2. [Communication and information](communication/index.md): fusion, KW games,
   rectangle covers, rank/discrepancy/corruption, information complexity, lifting,
   protocol composition and knowledge compilation.
3. [Algebraic and analytic methods](algebraic/index.md): polynomial approximation,
   Fourier/degree, derivatives and evaluation dimension, rigidity, tensor rank,
   monotone Boolean approximation, monotone arithmetic/tropical methods, algebraic
   geometry and representation theory. Keep real approximation and finite-field
   probabilistic polynomials separate.
4. [Graph structure, codes, and proof complexity](structural/index.md): separators,
   branch decompositions, brambles/tangles, matroids, coding, tensor contraction,
   pebbling, crossing sequences, with a dedicated child document for resolution,
   interpolation, polynomial calculus, and semialgebraic proofs.
5. [Algorithms, explicitness, and barriers](meta/index.md): counting,
   incompressibility, diagonalization, SAT/learning algorithms, hardness/randomness,
   explicit extractors and additive combinatorics, hardness magnification and its
   locality barrier, natural proofs, relativization, algebrization.

Ownership: communication owns representation semantics and protocol composition;
structural owns layouts and compilation; algebraic owns rank/tensor invariants;
combinatorial owns restriction accounting; meta owns explicit hard-set construction.
The final synthesis must give an exact missing lemma, numerical effect, smallest
falsification test, and stopping condition for each leading direction.

## Supplementary code

All checks use the Python standard library. The general mathematical claims have
proofs in the documents; finite checks validate examples and implementations.

- [Graph layout identities and nonlinear support counterexample](data/check_layout_identity.py).
- [Restriction, INDEX, composition, and numerical comparisons](combinatorial/data/check_claims.py).
- [Semantic transition compatibility and counting](communication/data/check_semantic_quotients.py).
- [Affine normality and algebraic transfer counterexamples](algebraic/data/check_bridges.py).
- [Truth-table propagation in the circuit CNF](structural/data/check_propagation.py).
- [Citation/link validation and aggregate rerun](data/validate.py).

Run `python3 research/lower-bound-vantages/data/validate.py` from the repository
root. Recorded outputs are linked from the [validation record](data/validation.md).

## Known Limitations

No improved unrestricted coefficient is claimed by this comparison. Existing
Lean theorems are not an audit of new proposed bridges. Results for signed tensor
contractions do not automatically provide positive splicing representations;
high rank, entropy, or communication demand at many cuts cannot be summed without
controlling reuse. Formal cover equivalences must preserve the basis and cost.
This is a systematic comparison of the major relevant families, not an exhaustive
historical bibliography or a priority claim. The new deductions are not Lean
formalizations. Computational experiments do not establish asymptotic layout
coefficients or global restriction coverage.
