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
- Same frontiers: linear maps and arithmetic circuits (Thm. 1.5, Cor. 1.6), aggregate gates
  (Thm. 1.7), and #SAT in time 2^{(1/4 + η)s}, or expected 2^{(0.2192 + η)s} (Thm. 1.8).
- Formally verified in Lean 4: all lower bounds and the layout theorem.

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
   |S| ≤ (K - 1)^2 Σ_t |transitions at t| (Lemma 3.2). Picture: a read-once program.
2. Networks (Sec. 4): local constraints on edges; separator lemma (Lemma 4.3); sweeping along a
   layout costs q^{frontier} transitions per step (Prop. 4.4, Thm. 4.5).
3. Compiler (Sec. 5): signals, junction chains (show the figure), exactness (Thm. 5.1);
   counting β₁ + |read| ≤ (r - 1)s + 1 (Prop. 5.4): gates make constraints, fan-out makes
   topology.
4. Demand and supply (Sec. 6): demand, a frontier carries about n values; supply, the layout
   has width about A(s - n); one comparison (Lemma 6.1) finishes every bound.

## 4. Layouts (17:00–21:00)

- Compression to simple cubic graphs (Prop. 7.2): factor two, h ≤ 2(β₁ - 1).
- Median layouts (Lemma 7.3): frontiers bounded by straddling vertices and window edges.
- Gaussian edge scores from kernel rows (Lemma 7.4); Sheppard at every threshold (Lemma 7.5);
  one vertex straddles with probability (3/2π) arccos((1 + 3ρ₀)/4) (Prop. 7.6).
- Correlation 2√2/3, as for Gaussian waves on the 3-regular tree.
- Limit of the method (Sec. 7.4): bisection of random cubic graphs means A ≥ 0.2066,
  coefficient at most 5.84.

## 5. Extensions (21:00–24:00)

- Linear maps: totally regular, Cauchy matrices, linear capacity, linearization by dual
  numbers (Sec. 8).
- Ledgers: guess the product, check it at the end; components (Sec. 9).
- Counting: dynamic program over frontier values; the minimum of brute force and the layout
  (Sec. 10). Not formalized.

## 6. Formalization and open problems (24:00–27:00)

- Lean 4 on CSLib and Mathlib; about 8,600 lines; standard axioms only; statements read like
  the paper; index in Appendix A.
- Design choices worth a sentence: one frontier sweep for everything, constants free, minimal
  layout hypothesis (Sec. 11).
- Open problems (Sec. 12): better LB_3(A); finer frontier measures beyond 5.84n; larger
  fan-in; nondeterministic circuits; explicit hard sets inside Lean.
