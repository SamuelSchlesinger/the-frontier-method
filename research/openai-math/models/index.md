# Circuit models and coherent representation transfer

[Corpus](../index.md) · [Existing synthesis](../../lower-bound-vantages/synthesis.md)

The most relevant contribution is a design discipline: replace a boundary by a
globally correct, composable description and pay for its entire implementation.
Family 124 supplies a scheduling example of this discipline; 129 shows why
two-way composition needs return behavior; 130 gives an exact linear restoration
identity. None supplies a compiler improving unrestricted Boolean Frontier.
The elementary deductions and finite checks below are additions to this synthesis,
not claims of historical novelty or newly checked Lean theorems.

## Resource comparison

Our target counts every positive-arity gate of an arbitrary-fanout, full-basis,
fan-in-two Boolean DAG. Constants are free. With `n` used inputs and `s` gates,
the existing demand and supply compare `log2 D >= n-o(n)` with
`log2 D <= A(s-n)+o(n)`, where `A=0.280701937...`. Here `D` counts retained
transitions, not just states. A replacement coefficient `B<A` gives `1+1/B`;
`B=1/4` would give five. These are the repository's existing conclusions.

| Family | Inspected source claim / selected formal scope | Resource that blocks direct transfer |
|---|---|---|
| 124 | Exact three-machine unit-job precedence scheduling in polynomial binary-input time | Jobs and precedence are not Boolean signal values; a three-job slot is not a bounded circuit cut. [oai124][oai124] |
| 129 | An `n`-state 2NFA whose complement needs at least `2^floor((n-4)/127)/2-1` states | Alphabet has `2^((n-2)^2)` letters; state count excludes the transition-table cost and input encoding. [oai129][oai129] |
| 112 | One language in P with depth-three OR–AND–OR size `2^omega(sqrt n)` | Unbounded fan-in, exactly three layers, free input negations; arbitrary sharing remains allowed. [oai112][oai112] |
| 130 | Exact complex DFT circuits have `liminf L(n)/(n log2 n)=0` | Arbitrary predetermined scalars, charged scalar multiplications, unrestricted conditioning; selected theorem is subsequential. [oai130][oai130] |
| 135 | Characteristic-zero homogeneous depth-five IMM size at least `n^(sqrt(n)/400)` eventually | Formal polynomials, syntactic homogeneity, degree `n`, `n^3` ambient variables; formal `circuitSize` includes leaves. [oai135][oai135] |
| 137 | One-writable-tape time `T` simulated in `T^(2/5) polylog(T)` space | Fixed machine, unit head motion, accessor hypothesis, finite-control outcome, unrestricted simulation time. [oai137][oai137] |

All source claims refer to snapshot `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
They are statements inspected in source, not independently established results.

## 124: bounded descriptions must remain valid globally

The scheduling manuscript's `paper.tex`, `lists.tex`, `boundary.tex`, and
`descriptions.tex` expose the relevant mechanism. It first pads a feasible
schedule to three jobs per slot. Its description language uses precedence cones
of triples, membership in triples, and rank thresholds in a fixed linear extension
or its reverse. With `N` jobs there are `O(N^3)` atoms. At most `K=10000`
formula leaves therefore give `O(N^(3K))` syntactic descriptions. The structural
claim actually uses fewer than 500 leaves, independently of recursive depth.
This is a very large polynomial, not an efficient practical algorithm. [oai124][oai124]

The dynamic-program states are compatible partitions `(L,Z,R)` of a described
job set, with `Z` an antichain triple. A transition requires
`L union Z subset L'` and prior acceptance of the smaller gap
`L' \ (L union Z)`. These conditions make the concatenated schedules sound.
Completeness requires one hierarchy in which all node sets and marked splits
admit the bounded descriptions; optimizing each interval separately would not do.

The delicate step is `lem:global-child`. A cutoff formula initially agrees with
its intended set only inside a known parent interval. Positive precedence cones
first locate a candidate in that interval, and exclusions then localize the child.
The construction avoids accumulating an ancestor-membership test at every level.
Its global past-boundary invariant and exchange invariant, quantified over every
future feasible local reordering, supply the missing external control. Pruned
lists contain at most five entries of fewer than 40 leaves each. [oai124][oai124]

**Transfer lesson.** A Frontier summary needs a corresponding contextual
invariant: two descriptions may be substituted only if every allowed continuation
has the same accepting behavior. A locally correct predicate with no domain guard
can introduce false splices. This agrees with, and does not newly prove, the
repository's [coherent semantic quotient](../../lower-bound-vantages/communication/index.md).
Scheduling reorderability and its fixed capacity three have no established
analogue for arbitrary Boolean DAGs carrying arbitrary truth tables.

**Quantitative deduction.** If a description has at most `k` leaves over `Q`
atoms, including their negations and constants, there are at most
`M=[16(Q+1)]^k` such formulas: multiply binary-tree shapes, connective choices,
and leaf labels, and sum over at most `k` leaves. If these descriptions already
form a coherent length-`n` binary acceptor, deterministic transitions cost at
most `2nM`; general nondeterministic transitions cost at most `2nM^2`.
Thus polynomially many atoms cost `Theta(k log(s+n))` bits, not `k` bits.
Correctness and a bounded leaf count alone do not recover the needed exponent.

## 129: four boundary relations, including returns

The complementation paper represents a segment by four relations on `m` labels
per direction: forward `F`, backward `B`, left-return `L`, and right-return `R`.
Joining neighboring segments allows arbitrarily many finite returns across the
join. In path-order relation multiplication, its formula is

```
F_(ab) = F_a (L_b R_a)* F_b.
```

The star includes the empty path. An automaton with `s` states gets `m=s+1`
labels per direction, using an added success state and a rightward exit routine.
Stay transitions are closed locally; infinite nonaccepting runs produce no finite
acceptance. The full diagrams compose associatively by path expansion and
contraction. The paper credits Martin and Mazorchuk's partitioned binary relation
monoid for this representation. [oai129][oai129]

**Local falsification test.** Let labels be `{0,1}`. Segments `a0,a1` both have
`F={(0,0)}` and empty backward and left-return relations. Only `a1` has
`R={(0,1)}`. Give a right context `b` the relations `L={(0,0)}`,
`F={(1,0)}`, with other relations empty. Then `F_(a0 b)` is empty, whereas
`F_(a1 b)={(0,0)}`. The latter path crosses `a1`, returns through `b`, returns
through `a1` with a changed label, and finally crosses `b`.
Thus even both through relations fail to determine contextual acceptance.
The [checker](data/check_model_transfers.py) verifies this using both the formula
and an independent joined-port reachability calculation.

**Where the cost goes.** Four arbitrary relations on `m` labels need `4m^2`
bits and admit `2^(4m^2)` possible summaries. This is an upper count of possible
diagrams, not a lower bound on realizable summaries of one machine.
If labels themselves encode all `2^k` assignments of `k` live Boolean values,
generic relation tables use `4*4^k` bits. Remembering every possible return
behavior is sound but supplies no small universal Boolean frontier description.
Nor do reachability diagrams preserve accepting-path multiplicities: they record
existence of paths, whereas an exact counting compiler must also control ambiguity.

The lower-bound mechanism requires a surjective multiplicative map from a diagram
submonoid to all relations on `h` points, reversing edge inclusion. Singleton
contexts detect missing pairs; recurrent-class losses then amplify through nested
idempotent corners. These are substantive hypotheses, absent from Frontier's
general accepted-set representations. A fixed-length binary encoding of arbitrary
relation letters needs `h^2` bits, and implementing a letter transition must be paid.
There is no constant-preserving state-to-Boolean-gate reduction here. [oai129][oai129]

## 130: an actual affine transfer, with nonlinear failure

The exact Fourier paper's `fft:dirty-layers` is useful independently of its main
Fourier theorem. For a linear DAG computing `Mx`, with `ell` gates, depth `H`,
fanout at most `delta` including output uses, it realizes
`(x,y,z) -> (x,y+Mx,z)` using `ell` scratch coordinates with arbitrary initial
contents. It bounds the cost by `8ell+2a` coordinate shears for `a` outputs and
`O((delta+1)(H+1))` disjoint-pair layers. A complex shear itself costs at most
two charged scalar gates. The source credits Bennett's uncomputation and
transparent computation by Buhrman and collaborators. [oai130][oai130]

Its forward sweep has the form `z -> Uz+Tx`. Read the output into `y`, reverse
the sweep, then replay with original-source edges removed, subtract its output,
and reverse again. The unwanted `FUz` cancels. Because this is a formal linear
identity in all coordinates, scratch values may already be correlated with `x`
and `y`. The Fourier construction uses this fact to fit convolution workspaces
inside existing coordinates rather than increasing tensor width.

**Constructive deduction.** The same identity holds over `F_2`; each nontrivial
shear is one XOR gate. A prescribed linear update can therefore borrow and restore
already occupied Boolean registers with at most `8ell+2a` XOR gates.
Affine offsets can be applied separately and charged. This is a usable restricted
compiler primitive, not a reduction in the total positive-arity gate count:
all replay gates count, scratch coordinates must exist, and an arbitrary-fanout
source DAG need not retain the displayed small layer bound.

**Failure beyond linearity.** Apply the same four-sweep recipe to gates
`g1=x1 AND x2`, `g2=g1 AND x3`, updating dirty scratch by XOR. After the original
and source-muted output reads, the target receives
`x1*x2*x3 + z1*x3` over `F_2`, rather than `x1*x2*x3`.
For `x=(0,0,1)`, `z=(1,0)`, `y=0`, it returns one instead of zero while restoring
both scratch bits. Exhausting all 64 input/target/scratch assignments finds 16
failures for this AND circuit and zero for the analogous two-XOR circuit.
Scratch restoration alone is insufficient; the output identity is essential.

The promising continuation is to isolate affine regions and measure whether
restoration reduces the *joint* transition budget after paying for their gates.
This extends the repository's existing affine-syndrome viewpoint, not its lower
bound. Stop any claimed full-basis replay rule on the two-AND example unless it
explicitly removes the cross-term and charges that removal.

## The other screens do not remove these obligations

Family 112's CNF correlation argument uses a signed restricted-CNF expansion with
controlled absolute coefficient mass. Signed cancellation is not a positive
accepting representation. Depth reduction would need a paid compiler and a demand
theorem for its actual output; the inspected depth-three result alone makes no
unrestricted-depth claim. It does not assert `2^(n^(1/2+epsilon))`. [oai112][oai112]

Family 135 retains sharing but restricts depth and formal degree. Boolean
arithmetization agrees only on Boolean inputs unless additional polynomial
identities are proved, and syntactic homogeneity is a further restriction.
IMM itself has polynomial-size unrestricted arithmetic circuits. Its lower bound
therefore does not certify arbitrary-DAG hardness at the Frontier resource. [oai135][oai135]

Family 137's space expression is `~O(b+(1+T/b^2)sqrt(b))`, balanced at
`b~T^(2/5)`. Fixed controller transcripts make single-block consistency factor;
simultaneously inspecting two independent blocks need not factor. The paper's
equality example `{00,11}` isolates this obstruction. Space without bounded
simulation time is not a small read-once representation. The paper explicitly
notes that quadratic one-tape conversion would turn original multitape time `T`
into `~O(T^(4/5))` space, not a general two-fifths exponent. [oai137][oai137]

## Precise next lemma and stopping condition

There is already a quantitative compilation antecedent: Amarilli, Capelli,
Monet, and Senellart's Theorem 4.4 constructs a complete unambiguous OBDD of
width at most `2^(2(k+1))` from a circuit and a supplied path decomposition of
width `k`. The compiler is singly exponential in `k`. Their Boolean basis and
circuit pathwidth must be related to our full-basis signal/cycle resource with
explicit constants; unambiguity is not determinism. The target below improves
the resource accounting, rather than merely asking for some coherent compiler.
[amarilli20][amarilli20]

Common structure can be expensive. Bova, Capelli, Mengel, and Slivovsky's
Proposition 14 gives size at least `2^h-1` for deterministic structured DNNFs
computing `OR_i(x_i AND y_i)` when the vtree contains all `x` variables as one
subtree. An interleaved OBDD reading each pair consecutively has linear size:
remember whether an earlier pair succeeded and the current first bit. Thus
forcing a shared decomposition can erase a compression gain; merely knowing
that two representations compute the same function does not transport their
weighted certificates to a common prefix tree for free. [bova16][bova16]

**Proposed coherent-description compiler, unproved.** Fix `B<A` and `c>5`. For every
full-basis `B2` circuit with `s<=cn` on `n` used inputs, construct one exact
layered acceptor, in one stated input order, accepting precisely its satisfying
assignments, with a unique accepting path per assignment and
`log2(number of retained transitions) <= B(s-n)+r(n)`, with `r(n)=o(n)` independent of the circuit.
An ordered read-once acceptor is one sufficient target, stronger than the current
coherent-sweep interface; a circuit sweep is not automatically such an acceptor.
Descriptions must determine sound continuation behavior and admit common
interlayer transitions, with no uncharged guesses or encodings.

For a nondeterministic formula-description construction, a sufficient budget is
`2k log2(16(Q+1)) + log2(2n) <= B(s-n)+o(n)`; a deterministic construction
can replace `2k` by `k`. At the five target, the generic nondeterministic
state-description exponent must therefore be at most `(s-n)/8+o(n)`.
Better outdegree control could avoid this square, but must be proved.
The scheduling theorem supplies neither this budget nor a Boolean compiler.

Test proposed rules on the contextual-return example and the dirty-AND example,
then on shared XOR prefixes with nonlinear continuations. Stop a rule if support,
path counts, or the retained-edge budget fails. Passing finite tests establishes
none of the required uniform asymptotic coverage. The existing semantic quotient
lemma already settles one correctness case; the missing result is the universal
quantitative compression theorem.

## Inspected formal scope and reproducibility

The five Comparator configurations select `ThreeMachine.main_theorem`,
`TwoWayComplementation.complementation_lower_bound_finite`,
`DepthThreeLowerBound.exists_polynomial_time_language_depth_three_lower_bound`,
`ExactFourier.main_theorem`, and `Problem335.main`, all under namespace `OAI`.
The corresponding solution declarations and their models were read. The scheduling
statement uses one fixed multitape machine and exponent `150020`; Fourier's
selected statement is subsequential, unlike the stronger all-length companion
described in the catalogue. No family-137 scope/config entry was located.
Comparator challenge files intentionally end their target statements with
`sorry`; they are not the proof implementations.

Upstream was **not rebuilt or imported**. Its inspected configuration pins Lean
`v4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, additional packages,
and compatibility-patch hooks. No independent kernel or axiom audit is asserted.
The local stdlib experiment is reproducible from the repository root:

`python3 research/openai-math/models/data/check_model_transfers.py`

Its expected output is [recorded here](data/check_model_transfers.expected.txt).
It additionally checks associativity on all 4,096 triples of one-label diagrams;
this is a finite consistency check, not a proof of arbitrary-size associativity.

[oai124]: ../sources.md#oai124
[oai129]: ../sources.md#oai129
[oai112]: ../sources.md#oai112
[oai130]: ../sources.md#oai130
[oai135]: ../sources.md#oai135
[oai137]: ../sources.md#oai137
[amarilli20]: ../sources.md#amarilli20
[bova16]: ../sources.md#bova16
