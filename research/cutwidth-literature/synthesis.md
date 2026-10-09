# What can actually improve the Frontier Method?

[Review home](index.md) · [Classical bounds](classical/index.md) ·
[Spectral methods](spectral/index.md) · [Structural methods](structural/index.md) ·
[Related parameters](parameters/index.md)

The review has not located a verified external theorem that can be substituted for
the current universal cubic bound to improve its coefficient immediately.
It has identified a concrete extension of the local-improvement machinery, a useful
short-cycle reduction, and two precise obstructions in classical transfer methods.
These are actionable findings, not a claim that the literature is exhausted or that
the unrestricted circuit coefficient has changed.

## Exact numerical targets

The baseline inspected in `Frontier/Layouts/Gaussian.lean`, `Frontier/Layouts.lean`,
and `Frontier/Layouts/Compression.lean` is

```
p = 3/(2*pi) * acos((1+2*sqrt(2))/4) = 0.1403509686358236...
A = 2p                                  = 0.2807019372716472...
L = 1 + 1/A                             = 4.562497678925021...
```

The required supply statement is a single ordering of each sufficiently large
simple cubic graph with **every** prefix cut at most `(c+epsilon)h+O(1)`.
The checked compression/restoration theorem transfers it to loopless subcubic
multigraphs with leading cycle-rank coefficient `2c` and logarithmic overhead.

| Desired binary coefficient `L` | Required cubic coefficient `c` | Saving from present `p` per vertex |
| --- | --- | --- |
| 4.6 | 0.138888888889 | 0.001462079747 |
| 4.7 | 0.135135135135 | 0.005215833501 |
| 4.8 | 0.131578947368 | 0.008772021267 |
| 5.0 | 0.125000000000 | 0.015350968636 |

The last target requires approximately a 10.94% decrease in the cubic coefficient.
These are arithmetic implications, not new graph theorems. They also describe the
required change for the existing exact, average-case, randomized, nondeterministic,
and linear-map transfers. The Hessian/determinant transfer uses its own demand factor.

The existing wire-layout route has a real but looser obstruction: random cubic
graphs have bisection width at least `0.103295h` asymptotically almost surely.
Since every order contains a bisection, a universal cubic coefficient must be at
least `0.103295`. This limits this particular universal wire-supply route to
`L <= 1+1/0.20659 ≈ 5.8405`; it does not rule out `5`, a different compiler,
or smaller semantic capacity. [lichev-mitsche2023][lichev-mitsche2023]

## First priority: small patches and nested minimum cuts

The best near-term direction is to extend the checked independent-vertex median
update in `Frontier/Layouts/Local.lean` to bounded patches with no edges between
different patches. For a threshold, fix the outside labels and minimize the cut
inside each patch. Choosing canonical minimum cuts makes the optimal interior
sets nested as the threshold increases; hence all thresholds come from **one set
of new vertex keys**. The [spectral review](spectral/index.md) connects this with
discrete coarea and parametric minimum-cut literature and supplies a paper argument
and finite checks.

What this resolves: independent fixed-threshold optimizations need not be compatible,
but this submodular construction gives a concrete compatibility mechanism.
What it does not resolve: monotonicity alone could save zero at the thresholds
where the original layout is largest.

The target theorem should use the original straddling budget `S_G(t)` and the actual
cut `C'_G(t)` after updates. It is enough to prove, for some fixed `delta>0`,

```
sup_t E[C'_G(t)] <= (p-delta) h + o(h),
```

uniformly over all cubic graphs, with bounded-radius dependence and window/tail
control sufficient to obtain a good sample and break ties. A more practical
certificate bounds the difference between the baseline budget and updated cost,
allowing extra baseline slack on short-cycle configurations. It need not force
positive update gain in every local type if an unmodified type already has slack.

Concrete work sequence:

1. Use one-vertex and two-vertex patches, then selected small trees/cycles; make
   the minimum-cut tie rule and patch separation explicit.
2. Enumerate rooted local graph types and the covariance constraints actually
   supplied by the truncated distance kernels.
3. Optimize the **joint** baseline-minus-gain objective near critical thresholds.
   Retain singular covariance cases, short cycles, and all patch ports.
4. Turn a successful numerical candidate into a rigorous bound, e.g. interval
   integration plus a certified covering or a proved covariance comparison.
5. Reuse the repository's finite-dependence grid argument, with new support and
   tie-window constants. Only then instantiate `CubicLayoutBound`.

The spectral review also shows why tightening the old median-charge inequality
alone is insufficient: its discrepancy can vanish at the extremal zero-threshold
tree distribution. Increasing only the old Gaussian correlation encounters the
tree spectral constraint. Both conclusions concern the existing construction;
neither rules out nonlinear patch updates or a different global construction.

## Second priority: short-cycle reductions with an explicit budget

The [triangle reduction](structural/reductions.md) is immediately usable as a
restricted-class theorem. Contract a packing of `t` vertex-disjoint triangles,
apply the existing multigraph supply theorem, and restore the triangles:

```
cw(G) <= (p+epsilon)(h-2t) + O_epsilon(log h).
```

The upper lifting cost is at most one for the entire expansion. This follows
from the paper proof and exact local enumeration; no Lean change is claimed.
The published triangle-expansion precedent is credited in that note.

This provides the easy side of a potential structural dichotomy. Extending it to
other bounded port gadgets, and proving that all remaining hard graphs admit a
uniform patch gain or suitable high-girth analysis, is the hard side. A positive
density of triangles gives a positive leading saving, but arbitrary cubic graphs
need not contain even one triangle.

Deleting vertices to get high girth is usually too expensive under the naive
restoration inequality. Treat every proposed reduction as a ledger: how much
cycle rank/vertex mass disappears, how much frontier cost returns, and whether
multiple restorations overlap at one prefix. No reduction earns a saving merely
because the residual graph is easier.

## Third priority: an anchored completion theorem

The [classical review](classical/index.md) finds that Fomin–Høie's proof retains an
`h/6` term even if one supplies a better bisection. The missing object is a better
layout of a half-graph with a prescribed boundary still available. This makes
boundary-aware pathwidth a more precise target than another unqualified bisection
algorithm. The exact subcubic conversion `cw<=pw+2` means a genuine universal
pathwidth improvement would transfer with no multiplicative loss.

This route may complement patches: decompose along genuinely cheap cuts and use
the local Gaussian construction on the remaining difficult pieces, retaining the
cost of all exposed ports. A tree separator bound must be upgraded to the union
of boundaries required by the repository's tree-merge theorem.

The [spectral separator and SDP review](spectral/separators.md) makes this global
route more concrete. Cheeger-type sweeps and reweighted vertex expansion can
identify useful separators, but their best-cut guarantees do not control the
largest frontier. Bansal–Katzelnick–Schwartz's direct `SDPCW` formulation is closer
to the target: it constrains the edge cost at every possible ordering pivot.
Their Section 6.3 leaves improved rounding open. A useful theorem here needs
both a favorable absolute relaxation value on cubic graphs and a sufficiently
small loss when converting it to one complete order. [bansal24][bansal24]

A complementary probabilistic route is to reorder small connected components of
a central score band. The [percolation discussion](spectral/index.md) identifies
the relevant Gaussian-wave literature and the missing median-band and arbitrary-
graph tail estimates. Existing tree percolation theorems do not supply that transfer.

## Fourth priority: semantic signal and code capacity

If wire cutwidth stalls, the existing signal hypergraph and joint-code theorems
provide a different supply target. The most compatible external frameworks are
matroid pathwidth/code trellises and symmetric submodular connectivity. They match
what the repository is already measuring more closely than adjacency-matrix
rankwidth or a generic tensor-contraction width. See
[the parameter conversion review](parameters/index.md).

The required statement remains quantitative and universal: one sweep/order of
each compiled circuit with a complete-transition exponent at most
`(1/4+o(1))(s-n)+o(n)` would reach the five target through the relevant demand
interface. The precise compiler must preserve all equations, all visible values,
and one common order. Separate good graph and code orders do not establish this.
For nonlinear gates a cut matrix of the underlying graph does not encode the
semantics automatically.

## What to use as experimental tools

Use exact subset dynamic programming or integer programming to obtain witnessed
optimal layouts on small cubic graphs. Compare the complete maximum frontier,
the baseline straddling count, patch gains, and signal/code costs on the **same**
orders. Include short-cycle-rich graphs and known expanding families, rather than
only random regular graphs. The [algorithmic review](classical/algorithms.md)
finds that the recent general cutwidth SDP was not competitive with MILP on its
very sparse benchmarks; SDP remains a useful probe, not an automatic first choice.

For larger graphs, heuristic improvements identify candidate inequalities. They
do not establish asymptotic constants. Certificates must bound the full continuous
covariance/threshold domain when that is the mathematical target, not only sampled
graphs, sampled thresholds, or successful optimization starts.

## Results that do not yet supply the desired improvement

| Attractive result or method | Exact missing transfer |
| --- | --- |
| Smaller random-cubic minimum bisection | Arbitrary graphs and an entire nested order |
| Maximum cut / maximum bisection / spin-glass asymptotics | Correct extremum, fixed degree three, and an all-prefix upper bound |
| Better eigenvector sweep cut | Maximum over all prefixes of that sweep |
| Better same-kernel star analysis | Existing extremal tree law attains the critical local value |
| Generic recursive separators | Inherited boundary costs and a useful numerical constant |
| New minor-free or geometric separators | A proved structural restriction on the compiled graph class |
| Edwards–McDermid with `g_3=p` | Its decreasing-increment inequalities already fail at degree four |
| Treewidth, carving width, or tensor contraction | Linearization or complete parent/children merge cost |
| Rankwidth, boolwidth, or mimwidth | An encoding theorem for the circuit's actual transition semantics |
| Exact/FPT/approximation cutwidth algorithms | A universal upper coefficient, not just a way to compute one instance |

## What was actually established in this review

- Verified source statements and hypotheses were matched to the repository supply
  contract; access depth is recorded source by source.
- The nested-patch construction and triangle lifting are explicit paper deductions,
  with reproducible finite checks. Neither has been added to Lean.
- Numerical target arithmetic, the classical reduction obstructions, and small
  conversion examples are independently checkable through the linked scripts.
- No new universal cubic coefficient, unrestricted circuit coefficient, complete
  literature census, or historical priority claim is asserted.

[bansal24]: sources.md#bansal24
[lichev-mitsche2023]: sources.md#lichev-mitsche2023
