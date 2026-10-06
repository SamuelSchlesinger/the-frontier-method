# What the comparison changes about the research plan

[Corpus](index.md) · [Sources](sources.md)

The strongest next step is a **restriction-or-compression theorem**. Retain the
existing demand, simplify where gates can be profitably removed, and use coherent
semantic compression on the residual cases. The survey supplies exact accounting,
correct semantic quotient operations, and a standard graph parameter to target.
It does not supply the missing universal coverage theorem or a coefficient above
`L=4.562497678925021...`.

## Common numerical scale

To compare methods fairly, write the logarithm of a sound representation's size as

```
log2 D <= a*s - b*n + o(n).
```

With the current demand `log2 D >= n-o(n)`, this gives
`s >= ((1+b)/a)*n-o(n)`, assuming `a>0`. Thus `a` alone is not the relevant
comparison. Our baseline has `a=b=A`; a quarter coefficient has `a=b=1/4`.
The depth-reduction budget `s/3.9` has `a=1/3.9,b=0`: despite `a<A`, it gives
only `3.9n` with a matching demand hypothesis.

For a representation of the form `B(s-n)`, the exact targets are:

| Desired lower-bound coefficient | Required `B` |
|---|---|
| Any fixed improvement over `L` | Any fixed `B<A=0.280701937...` |
| `4.6` | `1/3.6 = 0.277777...` |
| `4.75` | `1/3.75 = 0.266666...` |
| `5` | `1/4` |

The saving needed at `s=5n` is `4A-1=0.1228077491...` bits per input in the
representation exponent. Improving the leading coefficient is a different claim
from decreasing the `o(n)` remainder or the extractor error.

## 1. Bank restriction savings and pay for better terminals

**Established ingredients:** affine pullback of the target; the current frontier
terminal; existing safe gate-elimination rules; known weighted gate-elimination
and variety-volume methods. **Deduction in this corpus:** if step `i` loses `q_i`
dimensions and saves `g_i` gates net, and a terminal on `d` dimensions satisfies
`s_terminal >= L*d+H-o(n)`, then

```
s_initial >= L*n + sum_i(g_i-L*q_i) + H - o(n).
```

This lets a good phase pay for a later poor phase. A positive linear cumulative
surplus is enough for some improvement; every step need not save five gates, nor
must every terminal prove five on its own. The source, dimension, and density
hypotheses are stated in the [accounting lemma](combinatorial/index.md).

**Missing theorem:** every candidate circuit in a specified near-linear size
range has a restriction path retaining `d>=kappa*n` and satisfying
`sum(g_i-L*q_i)+H >= delta*n`, for fixed positive `kappa,delta`.
It would give `L+delta`. Five needs `delta>=5-L=0.4375023211...`.

**First test:** enumerate literal identifications and short affine substitutions
on low-fanout affine interfaces with nonlinear continuations. Record gate savings,
newly built parities, rank loss, and residual target dimension. A rule fails when
its substitution cost consumes its surplus. Finite coverage does not imply
unbounded coverage; any automated local search needs a structural completeness
lemma before it becomes a theorem.

## 2. Compress what a boundary can do, with compatible transitions

Communication supplies a concrete semantic replacement for a raw boundary value:
its complete accepting continuation behavior. The
[representative-series quotient lemma](communication/index.md) proves how to
merge identical behaviors without introducing false accepting paths or changing
counts. On a trim unambiguous acceptor, equality of right languages is sufficient
when one representative's outgoing edges are retained.

**Missing theorem:** every residual circuit in the required class admits such a
coherent acceptor with total retained transitions
`D <= 2^(B(s-n)+o(n))`, `B<A`. The quotient lemma proves correctness of a merge;
it does not bound how many equivalent states exist. Width alone is insufficient:
a nondeterministic width `W` can cost `O(nW^2)` edges.

**First test:** compile small circuits, calculate exact continuation languages,
and compare edge counts before/after quotienting with the existing joint affine
rank code. Include the three-bit compatibility and counting controls in the
checker. Stop a proposed local rule if it preserves separate cut covers but fails
the interlayer identities. A one-cut gain is useful evidence only after its
maximum-over-all-transitions cost is measured.

**Potential benefit:** semantic merging can use gate functions, not just topology.
That is precisely information the universal graph layout forgets. It can also
provide a terminal bonus `H` in direction 1, without requiring a universal
improvement for every graph.

## 3. Turn branching into a precise graph problem

The merge budget already present in the paper is exactly `tw(L(G))+1`, including
leaf costs. Combining the existing decomposable demand with Harvey--Wood's
identity gives the structural lower bound `tw(L(G))>=n-o(n)` for the compiled
bounded-degree networks. This is a paper deduction, not a new Lean result.
See [the full derivation](structural/joins.md).

**Missing theorem:** for the relevant connected subcubic graphs, prove
`tw(L(G))+1 <= B*beta1(G)+o(|V|)` with `B<A`. The conclusion would again be
`s >= (1+1/B)n-o(n)`. The quarter target is one precise stretch goal.

**First test:** search for extremal graph families and compute the exact join
parameter, using line-graph treewidth algorithms or bramble certificates. Individual
boundary sizes and `tw(G)` do not have the same constant. The finite checker
already detects a strict tree-versus-path difference on a ten-vertex tree; it
does not detect a strict saving on the named cubic examples. If an asymptotic
family violates the desired coefficient, stop that universal geometric claim
and retain the semantic or restricted-family alternatives.

**Potential benefit:** this is now a recognizable graph-theoretic theorem rather
than an informal hope that branching helps. Local code-constraint dimensions on
trees offer a further semantic extension, but need a matching additive tree-demand
lemma and one common decomposition for code and suffix.

## 4. Use the nonlinear gate count as a constraint, not an extra bill

The known affine-normality lemma implies that our sumset target needs
`n-ceil(log2 K)` nonlinear binary gates. The
[nonlinearity analysis](algebraic/nonlinearity.md) proves this with the output-hyperplane
loss included. With `log K=o(n)`, at least `n-o(n)` gates are nonlinear even if
affine operations were free.

Branching on both hyperplane values gives an average-case version: a circuit with
`k<=n-ceil(log2 K)-1` nonlinear gates agrees with a target of sign bias at most
`2b` on all large affine flats on at most `1/2+b` of inputs. The proof partitions
the entire cube into sufficiently large monochromatic affine flats for that
circuit, and averages the target's bias over them. This deduction tolerates
arbitrarily many affine gates; it is not a new total-gate bound or Lean theorem.

This is additional structural information about any candidate near `5n`. It
does **not** add another `n` to the total-gate lower bound. Both bounds charge
the same circuit.

**Missing theorem:** a paid mixed XOR/AND compiler or simplification theorem that
uses the location and dependencies of those nonlinear gates to yield a smaller
joint transition budget. Test AND trees, shared selectors, coded affine prefixes,
and arbitrary nonlinear suffixes. A universal negative discount merely for each
nonlinear gate is not justified. The useful statement is likely a dichotomy:
nonlinearity either permits a profitable restriction or forces compressible
boundary behavior. No such dichotomy is proved here.

## 5. Change the target only when the new geometry requires it

Nonlinear restrictions suggest variety dispersers or polynomial-source extractors.
Existing weighted-elimination and depth-reduction results demonstrate this route,
but their verified numerical consequences are below our baseline. Sumset extraction
does not supply arbitrary nonlinear-source hardness by a black-box reduction;
the [meta comparison](meta/index.md) gives the precise convex-mixture obstruction.

**Missing pair of theorems:** a paid compiler/simplification producing a specified
nonlinear source class at adequate entropy, and an explicit function dispersing
that class. Keep polynomial images and uniform points of varieties distinct.
Source parameters must meet the compiler's actual output, not a nearby source
definition. Reuse the existing target only if its additional property is proved.

This is a longer-term alternative. It may widen the allowable geometry more than
affine compression can, but currently requires work on both supply and demand.

## Transfers that the comparison rules out

| Attractive shortcut | Precise obstruction |
|---|---|
| Add the nonlinear-gate lower bound to the total-gate lower bound | They charge overlapping gates |
| Import quadratic formula shrinkage into unrestricted `B2` | Parity retains expected size at least `np-1+(1-p)^n` |
| Convert Nechiporuk cofactor count `R` into `log2 R` frontier bits | `N` nondeterministic states permit `2^N` cofactors; INDEX attains it |
| Optimize every communication cut separately | Minimum rectangle partitions can fail to admit common transitions |
| Merge states by unioning their outgoing transitions | Support can remain correct while accepting-path counts double |
| Use signed rank/evaluation dimension as a state count | Linear combinations cancel; INDEX separates dimension from deterministic residual count |
| Import matroid decomposition for log support sizes | A two-AND-gate distribution violates support-log submodularity: `9<10` |
| Sum information or rank over many cuts | Persistent shared values would be charged repeatedly |
| Improve the constant by lowering extractor entropy already in `o(n)` | This affects lower-order terms, not `A` |
| Infer a superlinear bound from maximal minor ranks alone | Generic linear-size superconcentrator circuits can realize all minors nonzero over infinite fields |
| Obtain arbitrary circuit lower bounds from proof hardness | A proof system's refutation resources are not the cost of generating a circuit trace |
| Invoke magnification on any explicit linear lower bound | Its hypotheses concern specified problems, promises, and input-length scales |

Each obstruction is proved, credited, or linked in the family documents. They are
filters for research proposals, not impossibility results for all extensions of
the underlying methods.

## Recommended next slice

Make one small exact experiment compare **net affine restriction surplus** and
**coherent semantic edge compression** on the same circuits. Include the current
joint-rank model as a baseline. Classify the residual cases on which both fail.
Those cases should determine the next structural lemma. In parallel, the graph
question is sufficiently precise to pursue as an independent theorem about
line-graph treewidth and cycle rank.

This recommendation is a synthesis of the comparison, not a report that the new
experiment, the coverage theorem, or an improved coefficient has been completed.
