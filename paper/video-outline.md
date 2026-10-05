# STOC 2027 video: outline (target 25 minutes)

Requirements (CFP): 20–30 minutes, presented by an author, explains the work, its context, and
its innovations relative to prior work. It may give motivation, intuition, and proof structure,
but must not add claims, corrections, or missing proofs. Due 2026-11-16 via HotCRP; reviewers
only. Every statement below is in the paper; section numbers refer to `frontier.pdf`.

## 1. Results (0:00–4:00)

- Circuits over a finite alphabet, any basis; count only inner gates (constants are free).
- Rectangle-free sets (Def. 2.2) and the layout bound LB_d(A) (Hyp. 4.1).
- Main theorem (Thm. 1.1): (r - 1) s > (1 + 1/A - ε) n.
- Gaussian layouts (Thm. 1.2): A ≈ 0.2807, so L ≈ 4.5625 for fan-in two (Cor. 1.3).
- An explicit language in P (Cor. 1.4), via sumset extractors (Chattopadhyay–Liao, Li).
- Existential witness inputs preserve the same lower bound, uniformly in their number
  (Sec. 6, theorem on nondeterministic circuits).
- Average case: extractor error b gives agreement at most
  1/2 + b + 2^{-Ω_ε(n)} for circuit size (L - ε)n. The weighted frontier lemma peels
  disjoint rectangles; unambiguity prevents overlapping contributions. A fixed gap below
  Ln is required. The weighted form uses input min-entropy and allows a shared exceptional
  measure. Lean checks weighted coherent sweeps and the uniform average-case circuit and
  sumset-bias theorems; the general distributional packing statements remain paper proofs.
- Same frontiers: linear maps and arithmetic circuits (Thm. 1.5, Cor. 1.6), aggregate gates
  (Thm. 1.7), and deterministic #SAT in time and space O*(2^{(1/L + η)s}), where
  1/L = 0.219178... (Thm. 1.8). O* suppresses polynomial factors in the full input size.
- Formally verified in Lean 4: the exact and uniform average-case lower bounds, arithmetic
  instantiations, and layout theorem. The explicit Boolean construction and its polynomial-time evaluation are cited.

## 2. Context (4:00–7:00)

- Gate elimination over the full binary basis: 2n, 2.5n, 3n - o(n), (3 + 1/86)n, 3.1n - o(n).
- The difference: no simplification of the circuit; charge the cycle rank of its wiring graph;
  one combinatorial property of the hard set; every basis at once.
- Cuts and width (Berman; Morizumi): cuts in evaluation order vs. cuts of the undirected
  constraint graph in any order (cutwidth).
- Fomin–Høie pathwidth gives A = 1/3, i.e. coefficient 4; the Gaussian layouts improve it.
- Linear maps: Valiant's superconcentrators vs. a single injective frontier (Lemma 8.3).

## 3. Proof structure (7:00–17:00)

1. Sweeps (Sec. 3): reveal coordinates in stages; splicing; the counting lemma
   |S| ≤ (K - 1)^2 Σ_t |transitions at t| (Lemma 3.2). Fixed-order read-once programs give
   sweeps; the converse for abstract sweeps is false (Remark 3.3).
2. Networks (Sec. 4): local constraints on edges; separator lemma (Lemma 4.3); sweeping along a
   layout costs q^{frontier} transitions per step (Prop. 4.4, Thm. 4.5).
3. Compiler (Sec. 5): signals, junction chains, exactness (Thm. 5.1); show the complete example
   and its frontier before any inputs are read (Fig. 1). Local consistency gives unambiguous
   programs directly (Prop. 5.3). Counting β₁ + |read| ≤ (r - 1)s + 1 (Prop. 5.5): gates make
   constraints, fan-out makes topology.
4. Demand and supply (Sec. 6): demand, a frontier carries about n values; supply, the layout
   has width about A(s - n); one comparison (Lemma 6.1) finishes every bound.

## 4. Layouts (17:00–21:00)

- Compression to simple cubic graphs (Prop. 7.2): factor two, h ≤ 2(β₁ - 1).
- Median layouts (Lemma 7.3): frontiers bounded by straddling vertices and window edges.
- Gaussian edge scores from kernel rows (Lemma 7.4); Sheppard at every threshold (Lemma 7.5);
  one vertex straddles with probability (3/2π) arccos((1 + 3ρ₀)/4) (Prop. 7.6).
- Correlation 2√2/3, as for Gaussian waves on the 3-regular tree.
- Limit of the universal layout hypothesis (Sec. 7.4): bisection of random cubic graphs means
  A ≥ 0.20659, coefficient at most 5.8405. A theorem restricted to compiler graphs could evade it.

## 5. Extensions (21:00–24:00)

- Linear maps: totally regular, Cauchy matrices, linear capacity, linearization by dual
  numbers (Sec. 8).
- Ledgers: guess the product, check it at the end; components (Sec. 9). Count only ordinary
  positive-arity gates. Modular counts have fixed moduli, or total logarithmic cost o(n).
- Counting: dynamic program over frontier values; the minimum of brute force and the layout
  (Sec. 10). Keep m reachable inputs: exponent min(m, A(s-m)) + ηs. For 3n and 4n gates,
  with all inputs reachable, this gives 0.5614n and 0.8421n plus arbitrarily small linear slack.
  Finite ledgers add a polynomial factor in |M|. Fixed local precision and conditional
  expectations give deterministic cubic layouts in f(ξ) h^3 polylog(h) time with an absolute
  polynomial degree. These algorithms and their complexity bounds are not formalized.
- Signal states: one value per distinct circuit signal, with a formally checked capacity
  inequality and a paper proof of exact counting (Sec. 5).

## 6. Formalization and open problems (24:00–27:00)

- Lean 4 on CSLib and Mathlib; about 10,000 lines; standard axioms only; statements read like
  the paper; index in Appendix A.
- Design choices worth a sentence: one frontier sweep for everything, constants free, minimal
  layout hypothesis (Sec. 11).
- Open problems (Sec. 12): better LB_3(A); finer frontier measures beyond 5.84n; larger
  fan-in; a smaller universal signal-layout coefficient; explicit hard sets inside Lean.
  The present local Gaussian estimate is sharp in its cubic-tree limit; this alone does not
  show global optimality of the layout coefficient.
