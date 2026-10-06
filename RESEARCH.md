# Boundary refinements: checked results and remaining targets

The paper's universal binary-circuit coefficient remains
`L = 1 + pi / (3 arccos((1 + 2 sqrt(2))/4)) = 4.562497…`.
The results below are kernel-checked refinements of the method. None asserts a smaller
universal cubic layout coefficient. The explicit extractor construction and all runtime
claims remain outside the formalization.

## Polynomially small average-case advantage

`averageCase_sumset_polynomial` checks that a flat-source extractor error at most
`C n^(-a)` gives agreement at most `1/2 + (C+1)n^(-a)` below `(L-epsilon)n` gates,
for every fixed positive gap. It retains the sole entropy condition `log K = o(n)`.
[Chattopadhyay and Liao, Theorem 1](https://eccc.weizmann.ac.il/report/2021/147/revision/1/download/)
supplies polynomially small error at polylogarithmic entropy; the first output bit therefore
gives the explicit `1/2+n^(-Omega(1))` corollary. That construction and its uniform
polynomial-time evaluation are cited, not formalized.

This is a separate instantiation from Li's logarithmic-entropy, constant-error family,
whose polynomial rectangle threshold supplies the stronger DNNF remainder `O(log n)`.

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
the MDS property. `mds_gaussian` gives the binary coefficient `L`; `mds_degree` supplies
the Gaussian coefficient for every fixed fan-in, including `7/4` at fan-in three.
`TotallyRegular.isMDS` and
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

`Gaussian.multigraph_vertexLayout_bound` improves the graph estimate in every fixed degree `d ≥ 2`:
loopless multigraphs have width at most `gamma_d |E| + o(|V|)`, where
`gamma_d = arccos(2 sqrt(d-1)/d) / pi`. The truncated-kernel correlation, bounded-radius
second moments, threshold grid, windows, tails, and ordering with ties are all checked.

Terminal block compression retains every edge between blocks, including parallel edges.
Its degrees are between three and `d`, and each adjacent pair has degree sum at least
`d+3`. `Multigraph.core_density` charges weight `d+3-a` per incidence at a vertex of
degree `a`, proving `3dh ≤ (d+3)m`. The compression ledger then gives
`(2d-3)m ≤ 3d beta1(G)` (`Compression.Terminal.multi_edge_bound`). Concentration counts
each edge separately: bounded degree controls multiplicity in the overlap estimate.

Consequently `layoutBound_degree` proves `LayoutBound d a_d`, where
`a_d = 3d/(2d-3) · gamma_d`. Lean also checks `0 < a_d < 3/4` and `a_4 = 2/5`.
`lowerBound_degree` proves `(r-1)s > (1+1/a_(r+1)-epsilon)n`, and
`linear_finite_degree`, `linear_polynomial_degree`, and `mds_degree` give the map versions.
The ternary coefficient is `7/4`; the fan-in-four coefficient is approximately
`1.092760448`. The median-edge argument remains sharper for binary circuits.
The paper derives deterministic counting with gate exponent `(r-1)a_(r+1)/(1+a_(r+1))`,
including `4/7` for ternary gates; the algorithms and their runtimes are not formalized.
No optimality or priority claim is made.

The remaining question is whether a joint degree/correlation analysis improves `a_d`.
Joint signal routing and subcubic port-tree projection are other possible routes,
but their universal congestion bounds remain to be proved.

## Verification

Run `lake build --wfail` and `lake env lean scripts/Audit.lean`. The audit contains exact
standard-axiom guards for forty-four principal endpoints. The paper includes proofs and
a declaration index for the added results, with external constructions and unformalized
algorithmic consequences identified separately.
