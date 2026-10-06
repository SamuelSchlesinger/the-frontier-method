# Boundary refinements: checked results and remaining targets

The paper's universal binary-circuit coefficient remains
`L = 1 + pi / (3 arccos((1 + 2 sqrt(2))/4)) = 4.562497…`.
The results below are kernel-checked refinements of the method. None asserts a smaller
universal cubic layout coefficient. The explicit extractor construction and all runtime
claims remain outside the formalization.

## Signals, hypergraphs, and codes

`Compiler.signalCut_eq_hypergraph_cut` identifies crossing signal labels with the native
hypergraph cut. Its proof establishes connectivity of every signal's occurrence graph;
the equality would be false for an arbitrary edge labelling. `signalCut_submodular`
then makes signal capacity a symmetric submodular connectivity function.

`Sweep.transitionCount_le_codes` allows any code that determines the entire transition.
`LinearBoundary.completions_eq_iff` and `ncard_syndromes` identify exact feasible states
of `L x + R y = 0` with `im L ∩ im R`. Their dimension is
`rank L + rank R - rank [L R]`. All gate equations must be included in the split system.
No claim is made that every Boolean frontier has a linear code or that separate ranks
of the two messages determine their joint transition.

The next numerical target is a universal ordering theorem for **joint signal or code
capacity** of compiled networks. A rank saving in one network, or an arbitrary change of
representation, does not establish that theorem.

Source: Navin Kashyap, [Matroid Pathwidth and Code Trellis Complexity](https://arxiv.org/abs/0705.1384).

## Pruning

`Sweep.abs_sumOn_le_pruned` and `agreement_le_pruned_sweeps` keep inputs whose complete
trace uses selected transitions. Coherence and nested revealed sets preserve splicing.
The discarded weight is bounded by a union bound, without independence assumptions.
Discarding total uniform probability mass `delta` costs `delta/2` in agreement after the
two output classes are combined.

The next target is a theorem giving small retained transition sets with a small tail
budget uniformly for all circuits in the size range. Small Shannon entropy alone does
not provide exponentially small tails; neither does a low average number of frontier
wires. A high-probability codebook or a stronger information-spectrum estimate is needed.

The weighted peeling argument underlying this extension is credited to Sam McGuire in
the paper's acknowledgments.

## Trees of regions

`TreeFrontier.abs_sumOn_le_of_budget` proves weighted peeling with residual factor
`(K - 1)^3` times the number of joint merge records. `Network.abs_sumOn_accepted_le_tree`
constructs the frontier from a laminar decomposition and unique satisfying traces,
assuming every input is read. Its exponent is the size of the **union** of the parent
and both child boundaries, plus locally read coordinates.

The next target is a decomposition with smaller joint merge capacity for all compiled
networks. A bound on the largest individual separator, or a generic conversion to a
tree-structured circuit with unspecified constants, does not suffice. If it has only
polynomially many nodes, the extra `(K - 1)` factor is harmless when `log K = o(n)`.

Relevant precedents are [Bova, Capelli, Mengel, and Slivovsky](https://www.ijcai.org/Proceedings/16/Papers/147.pdf)
on knowledge compilation and communication, and
[Markov and Shi](https://arxiv.org/abs/quant-ph/0511069) on tensor contraction widths.
These connections motivate the formulation; no external width equivalence is assumed
by the checked theorem.

## Decomposable representations

`Decomposable.ncard_le` proves the finite threshold bound directly for smooth union/product
DAGs: `|S| ≤ (K-1)^2 e_union + (K-1)^3 v_product` for a `K`-rectangle-free accepted set,
`K ≥ 2`, and `|S| ≥ K`. The checked `Occurs.substitute` theorem derives the context
rectangle from the DAG semantics. No determinism of union gates or uniqueness of accepting
certificates is assumed.

The paper deduces almost-full-exponential DNNF lower bounds, with an `O(n)` smoothing
conversion for nonsmooth Boolean DNNFs. That conversion is not formalized. The finite
theorem does not extend the weighted coherent-peeling result to arbitrary overlapping
certificates. Improving the circuit coefficient still requires a universal supply bound
for joint merge capacity.

## Mixed input-output fibers

`OutputSplicing.card_le` bounds the domain size by the number of used boundary messages
times the largest fibers of two complementary mixed observations. The compiler instance,
`Compiler.pow_le_cutSignals_mul_fibers`, charges distinct signals. This is a pointwise
demand theorem for arbitrary maps over finite alphabets.

`lowerBound_mds` transfers any positive layout coefficient to maps whose graph codes have
the MDS property. `mds_gaussian` gives the binary coefficient `L`; the same transfer with
`layoutBound_two_fifths` gives the ternary coefficient `7/4`. `TotallyRegular.isMDS` and
`IsMDS.permute` check the linear specialization and preservation under coordinatewise
alphabet permutations. The alphabet may grow with the dimension.

The next demand extension is the graded rank profile for ordinary matrices, with a
precise terminal-ordering parameter and componentwise accounting. Neither that matroid
pathwidth transfer nor the Jacobian extension is claimed by the present formalization.

## Nonlinear local updates

`LocalLayout.cutSize_improve_cubic_le` updates an independent set of vertices to the
median of their neighbours' original keys. Every real threshold cut weakly decreases.
`Multigraph.cutSize_eq_add_gain` gives the exact sum of local gains, and
`cutSize_lt_of_local` gives strict decrease when one selected vertex improves.

To obtain a new Gaussian constant still requires:

1. A positive linear expected gain at the thresholds controlling the maximum cut,
   uniformly over all cubic graphs, including those with short cycles.
2. Simultaneous concentration over a threshold grid, with window and tail control.
3. A bound on ties when the updated keys are converted into a vertex order.

The pointwise guarantee requires an independent update set. Simultaneously replacing
every vertex by a neighbour median is a different rule and has no such checked guarantee.
Numerical experiments on the limiting regular tree are not evidence of a uniform bound
on arbitrary graphs. Local Gaussian cut modifications and tree experiments already appear
in [Lichev and Mitsche, Section 6](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v30i2p40/pdf/).

## Every fixed degree and higher fan-in

`Multigraph.exists_layout_cycleRank` proves
`cutwidth(G) ≤ beta1(G) + d floor(log2 |V|)`.
`layoutBound_one d` absorbs the logarithmic error and proves `LayoutBound d 1` for every
fixed degree. `lowerBound_all_fanIn` consequently proves
`(r - 1)s > (2 - epsilon)n` for every fixed `r ≥ 2` and the same dense rectangle-free
families as the main theorem. This is a baseline, not a priority or optimality claim for
higher-fan-in circuit bounds.

`Gaussian.vertexLayout_bound` improves the graph estimate in every fixed degree `d ≥ 2`:
simple graphs have width at most `gamma_d |E| + o(|V|)`, where
`gamma_d = arccos(2 sqrt(d-1)/d) / pi`. The truncated-kernel correlation, bounded-radius
second moments, threshold grid, windows, tails, and ordering with ties are all checked.

For degree four, terminal block compression produces a simple core with degrees three
or four and no adjacent degree-three vertices. Weighting incidences proves `12h ≤ 7m`
and hence `5m ≤ 12 beta1(G)`. Since `gamma_4 = 1/6`, `layoutBound_two_fifths` proves
`LayoutBound 4 (2/5)` for the multigraphs needed by the compiler. The checked
`lowerBound_fanInThree` gives `s > (7/4 - epsilon)n`; the finite-field and polynomial
linear-map versions are `linear_finite_fanInThree` and `linear_polynomial_fanInThree`.
The paper also derives the deterministic ternary counting exponent `4/7`; the algorithm
and its runtime are not formalized. No optimality or priority claim is made.

For degree five and above, the proposed sharper cycle-rank constants still require a
multigraph compression and correlation argument: terminal quotients can have parallel
edges. The simple-graph per-edge theorem alone does not prove the proposed `LayoutBound`
coefficient. Joint signal routing and subcubic port-tree projection are other possible
routes, but their universal congestion bounds remain to be proved.

## Verification

Run `lake build --wfail` and `lake env lean scripts/Audit.lean`. The audit contains exact
standard-axiom guards for thirty-six principal endpoints. The paper includes proofs and
a declaration index for the added results, with external constructions and unformalized
algorithmic consequences identified separately.
