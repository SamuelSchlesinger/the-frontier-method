/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Rectangle
public import Frontier.Sweep
public import Frontier.Multigraph
public import Frontier.Network
public import Frontier.Compiler
public import Frontier.Compiler.Forest
public import Frontier.Demand
public import Frontier.Reduction
public import Frontier.LowerBound
public import Frontier.Layouts
public import Frontier.Main
public import Frontier.Extractor
public import Frontier.AdditiveSweep
public import Frontier.Parity
public import Frontier.Parity.LowerBound
public import Frontier.Parity.Matching
public import Frontier.Linear.Main
public import Frontier.Arithmetic.Determinant
public import Frontier.Components
public import Frontier.Ledger.Main
public import Frontier.Nondeterministic
public import Frontier.Signals
public import Frontier.AverageCase.Extractor
public import Frontier.Randomized
public import Frontier.AverageCase.Additive
public import Frontier.Boundary.Code
public import Frontier.Boundary.Joint
public import Frontier.Boundary.Syndrome
public import Frontier.Boundary.Observation
public import Frontier.Boundary.Forest
public import Frontier.AverageCase.Pruning
public import Frontier.Boundary.Communication
public import Frontier.Tree.Network
public import Frontier.Layouts.Local
public import Frontier.Layouts.Patch
public import Frontier.Layouts.GaussianPatch
public import Frontier.Layouts.GaussianStability
public import Frontier.Layouts.GaussianQuantitative
public import Frontier.Layouts.Pair
public import Frontier.Layouts.StarStability
public import Frontier.Layouts.StarSupply
public import Frontier.Layouts.Packing
public import Frontier.Layouts.KernelRigidity
public import Frontier.Layouts.KernelStability
public import Frontier.Layouts.KernelCovariance
public import Frontier.Layouts.KernelPairStability
public import Frontier.Layouts.PairGeometry
public import Frontier.Layouts.MatchingLayout
public import Frontier.Layouts.MatchingMean
public import Frontier.Layouts.MatchingLocal
public import Frontier.Layouts.MatchingGrid
public import Frontier.Layouts.MatchingGaussian
public import Frontier.Layouts.MatchingSupply
public import Frontier.Layouts.Incidence
public import Frontier.Decomposable
public import Frontier.Boundary.Fiber
public import Frontier.Boundary.Rank
public import Frontier.Boundary.MDS

/-!
# The frontier method

A circuit lower bound from graph layouts, in independent pieces:

* `Frontier.Rectangle`: rectangle-free sets, the only property of the hard set, and the support
  lemma. `Frontier.Extractor`: sumset dispersers have rectangle-free fibers.
* `Frontier.Sweep`: abstract splicing messages and the frontier counting lemma
  `Frontier.Sweep.ncard_le`. `ncard_le_charged` counts only transitions receiving
  a threshold charge; `ncard_le_charged_codes` accepts codes only on their charged
  inputs. No graphs or circuits appear.
* `Frontier.AdditiveSweep`: sumset-free sets require large additive generators;
  emitted vectors can overlap in their coordinate supports. Finite transition codes
  can charge one determined syndrome update rather than two independent states.
* `Frontier.Parity`: supplied input graphs preserve sumset-freeness and additive
  charging demand. Invertible additive input bases preserve the full circuit
  coefficient; arbitrary linear redundancy requires a further supply proof.
  `Frontier.Parity.LowerBound` proves the unrestricted promise-correct bound with
  the explicit loss `(1/A - 1) * readRedundancy`; sublinear redundancy preserves
  the leading coefficient. `Frontier.Network.Read` discards unused supplied inputs.
  `Frontier.Parity.Matching` uses the strict supply gain to preserve the old
  Gaussian coefficient for up to `10⁻⁴⁸ n` free extra parities.
  Arbitrary linear redundancy is still open.
* `Frontier.Multigraph` and `Frontier.Network`: layouts, the layout hypothesis
  `Frontier.LayoutBound`, constraint networks, the separator lemma, and the sweep of a network
  along a layout.
* `Frontier.Compiler`: circuits of fan-in `r` with any outputs, over any basis, become exact
  constraint networks of maximum degree `r + 1` and cycle rank at most `(r - 1) s + 1 - |read|`.
  `Frontier.Compiler.Source`: one-source compressed blocks form a forest and their port
  values depend on one input value. `Frontier.Compiler.Forest` bounds realized boundary
  patterns using this forest, assuming the reachable signals are nonconstant.
* `Frontier.Demand`: demand and supply, the comparison that ends every lower bound.
* `Frontier.Reduction` and `Frontier.LowerBound`: a small circuit yields a graph of small cycle
  rank all of whose layouts are wide; the layout hypothesis finishes the proof.
* `Frontier.Layouts`: Gaussian cycle-rank layout bounds in every fixed degree, including
  the sharper median-edge estimate for subcubic graphs.
  `Frontier.Layouts.Local`: independent median updates
  cannot increase any threshold cut.
  `Frontier.Layouts.Patch`: submodularity gives one set of keys minimizing every
  threshold inside a patch, including a common signal-boundary and parity-syndrome
  objective. Prefix bounds explicitly account for ties; a quantitative saving
  in terms of the gate count remains unproved.
  `Frontier.Layouts.GaussianPatch`: a uniform local gain for the symmetric
  two-vertex Gaussian model, invariant under realizations of its Gram matrix.
  `Frontier.Layouts.Pair`: explicit pair keys attain all threshold minima;
  subdivision costs bound actual graph cuts and account for prefix ties.
  `Frontier.Layouts.KernelRigidity`: exact critical edge ratios and saturated
  stars force that covariance; squared star residuals quantitatively control
  every covariance error. Joint rounding handles approximate ratios.
  `Frontier.Layouts.KernelStability` and `KernelCovariance`: correlation slack
  controls the ratio error of the actual finite kernels, including normalization
  and truncation. `StarStability` controls those correlations and residuals
  by the gap in the three-edge star inequality, giving a local covariance
  bound from two measured star gaps. `StarSupply` retains a definite saving
  from large gaps through concentration and all prefix cuts. `Packing` selects
  linearly many disjoint small-gap pairs in the complementary case.
  `GaussianStability` and `KernelPairStability` retain the local pair saving
  under covariance errors and small finite-kernel star gaps, uniformly over
  thresholds. `PairGeometry` supplies the actual graph incidences, and
  `MatchingLayout` assembles disjoint pairs into one key with controlled ties.
  `MatchingMean` supplies common parameters and a strictly improved expected
  cost for every cubic graph at every fixed threshold. `MatchingLocal` proves
  a second-moment deviation bound for that cost. `MatchingGrid` and
  `MatchingGaussian` combine all grid costs, windows, tails, and ties into one
  ordering with a universal coefficient strictly below the original Gaussian
  coefficient. `GaussianQuantitative` certifies the covariance tolerance, and
  `MatchingSupply` transfers a supply saving of `10⁻⁴⁸` to a circuit-coefficient
  gain of at least `10⁻⁴⁷`. The quarter supply coefficient and full
  redundant-parity preservation remain unproved.
  `Frontier.Layouts.Incidence`: signing incidence vectors cannot improve a prescribed
  family of cuts; exact accounting for the two sign classes.
* `Frontier.Linear`: totally regular linear maps, over finite fields with any basis and over
  infinite fields with polynomial operations; Cauchy matrices and arithmetic circuits.
* `Frontier.Arithmetic`: mixed-Hessian rank bounded by actual circuit frontiers over every
  field; scalar-polynomial gate bounds from input-order Hessian demand, including
  determinant demand `n²/4 - 3n` and the coefficient `1.8906244197…` for determinant circuits.
* `Frontier.Ledger` and `Frontier.Components`: gates of unbounded fan-in that aggregate in a
  monoid, carried along the layout as a ledger.
* `Frontier.Projection` and `Frontier.Nondeterministic`: existentially hiding inputs and the
  same lower bound for nondeterministic circuits, uniformly in the number of witness inputs.
  Polynomial-size binary verifiers pay one additional gate per distinct reachable witness.
* `Frontier.Signals`: frontier capacity measured by distinct circuit signals.
* `Frontier.AverageCase`: coherent weighted peeling and average-case circuit hardness from
  rectangle bias or sumset bias, with an exponentially small remainder below `L n`.
  Polynomially small sumset bias gives polynomially small agreement advantage.
  `Frontier.AverageCase.Additive`: coherent additive peeling with unique sum representations.
* `Frontier.Randomized`: arbitrary independent random mixtures preserve distributional
  success bounds. Fixing circuit coins preserves gate count and fan-in, so the average-case
  bounds also hold for randomized circuits, with an input witnessing the same success bound.
* `Frontier.Boundary`: hypergraph signal boundaries, exact linear syndrome states, and
  transition codes; mixed input-output fiber demand and nonlinear MDS lower bounds.
  `Frontier.Boundary.Rank`: graded linear observation ranks and terminal pathwidth demand.
  `Frontier.Boundary.Joint`: joint ranks of shared linear information and visible
  observations, avoiding independent charges for overlapping information.
  `Frontier.Boundary.Syndrome`: a sweep enforcing an additive consistency promise,
  paying one syndrome per transition. `Frontier.ncard_le_parity_sweep` applies it to
  circuits' accepting sets on consistently supplied parities, retaining the syndrome cost.
  `Frontier.Boundary.Observation`: the exact joint rank of visible input coordinates
  and the partial syndrome, including its use in the promise-enforcing sweep.
  `Frontier.ncard_le_parity_joint_codes` gives the resulting finite demand bound for
  original inputs together with redundant supplied parities.
  `Frontier.Boundary.Forest`: exact rank and capacity savings for overlapping equality
  scopes whose intersection graph is a forest, including Boolean complements and a
  full-transition code bound. The quarter supply theorem remains open.
  `Frontier.Decomposable`: threshold counting for smooth union/product DAGs with
  overlapping certificates. `Frontier.AverageCase.Pruning`: transition deletion with an
  explicit tail budget. `Frontier.Tree`: weighted peeling on trees of regions, with joint
  merge capacity.
  `Frontier.AverageCase.Capacity`: capped transition masses and square-root moments.
  `Frontier.Boundary.Communication`: conditional prefix potentials for dependent encodings.

The main theorem is `Frontier.lowerBound`: under `LayoutBound (r + 1) A`, circuits of fan-in at
most `r` deciding dense rectangle-free sets satisfy `(r - 1) s > (1 + 1/A - ε) n`. For fan-in
two this is `s > (L - ε) n` with `L = 1 + 1/A`. The layout bound holds with
`A = (3/π) arccos ((1 + 2√2)/4)` (`Frontier.layoutBound_gaussian`), giving the unconditional
`Frontier.lowerBound_gaussian`, with `L ≈ 4.5625`, and `Frontier.lowerBound_four`. The same
coefficient holds for totally regular maps (`Frontier.lowerBound_linear`,
`Frontier.arith_cauchy_gaussian`) and with sublinearly many fixed-monoid aggregate gates
(`Frontier.lowerBound_ledger`, `Frontier.lowerBound_aggregate_gaussian`).
The degree-four coefficient `2/5` gives `s > (7/4 - ε)n` for fan-in three
(`Frontier.lowerBound_fanInThree`). Finite-alphabet MDS maps inherit these coefficients
through `Frontier.lowerBound_mds`.
For every fixed `r ≥ 2`, `Frontier.lowerBound_degree` gives
`(r - 1)s > (1 + 1/A_(r+1) - ε)n`, where `A_d = 3d/(2d-3) * arccos(2√(d-1)/d)/π < 3/4`.
-/
