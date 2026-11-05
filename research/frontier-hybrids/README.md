# Failed and incomplete routes for extractor–frontier hybrids

Authors: Christian Reitwiessner

Research record: November 5, 2026. Repository baseline: `2fec7ab`.

This catalogue records the routes investigated in an exploration of extractors,
multi-output frontiers, chronological segments, and size–depth tradeoffs. “Failed”
means that a specific proposed implication failed, not that the entire technique
is useless. This is a record of this exploration, not an exhaustive history of
circuit lower bounds. No improvement to the repository's unrestricted circuit
bound or new formally checked theorem is claimed.

Read alongside the [general comparison of lower-bound methods](../lower-bound-vantages/index.md),
the [communication research](../communication/README.md), and the
[formalization guide](../../docs/FORMALIZATION.md). Short proofs of the main
counterexamples and accounting identities are collected in [proofs.md](proofs.md).
These are paper arguments, not Lean formalizations. Numerical experiments are not
used to certify asymptotic claims.

## Models and status labels

Unless stated otherwise, a Boolean circuit has fan-in at most two, arbitrary
Boolean gates, unrestricted fan-out, and size equal to its gate count. XOR/AND
constructions count XOR gates as well as AND gates. Multiplicative complexity
counts only AND gates and gives affine operations for free. Logarithmic depth,
unbounded-fan-in wire complexity, field-operation complexity, and sequential
workspace are distinct restrictions/resources.

- **Refuted:** a counterexample disproves the stated universal implication.
- **Insufficient:** a valid estimate or model conversion misses the needed scale.
- **Restricted result:** the argument works under additional hypotheses that
  have not been obtained from arbitrary circuits.
- **Open bridge:** no counterexample to the precise target is established here,
  but a required structural theorem is missing.
- **External conditional route:** a conclusion depends on an external conjecture;
  recent preprints are identified as such.

Here $n$ denotes the number of Boolean input bits, $s$ gate count, $q$ the number
of shared bits, and $\ell$ the number of raw inputs accessible to one local
decoder. An affine disperser at dimension $k$ is nonconstant on every affine
subspace of dimension at least $k$. A sumset disperser must be nonconstant on
every sumset in its specified source-entropy regime.

## A. Source structure and changing cuts

### A1. Improve the extractor and obtain superlinear size from the same layout bound

**Insufficient.** The existing reduction has a constant-coefficient exponential
representation upper bound, while the source demand has exponent at most order
$n$. Making an already sublinear entropy threshold smaller improves a remainder
or parameters; it does not change that comparison into a superlinear gate bound.

**What survives:** better extractor parameters and better layout constants remain
useful. A superlinear conclusion requires a different quantitative supply theorem,
an additional restriction such as depth, or a stronger computational invariant.
This does not say the current layout coefficient is optimal.

### A2. Replace two independent sources by many independent parts automatically

**Open bridge.** A frontier assignment separates a computation only along the
interfaces actually fixed. Multiple outputs or more segments do not, by themselves,
produce several independent high-entropy sources. One must prove the joint
factorization and pay for the union of boundary information.

**What survives:** fixing all interfaces of a genuine network partition yields
an exact product over its disjoint input blocks. Any two groups of sufficiently
large factors then give a sumset. A3, A10, and A11 explain why a universally small
conditioning cost cannot be assumed.

### A3. Every cheaply computed quadratic graph contains a large sumset

**Refuted at constant entropy rate.** There are quadratic maps
$P:\mathbb F_2^m\to\mathbb F_2^{O(m)}$ with $O(m)$-gate,
$O(\log m)$-depth circuits whose graphs contain no $A+B$ with
$|A|\ge3$ and $|B|\ge2$. A good linear encoder, constant-size block amplification,
and coordinate-pair products make the polar map nonzero on every independent
pair of directions. The graph is therefore Sidon. See [the construction](proofs.md#p1-cheap-quadratic-graphs-can-be-sidon).

**What survives:** this refutes exact containment and exact mixtures of large
sumset sources. It does not establish a statistical-distance obstruction for
approximate mixtures, and it does not cover output length $o(m)$.

### A4. Extend that counterexample to every high-rate quadratic graph

**Insufficient, with a positive regime.** A Sidon graph of $2^m$ points in
$\mathbb F_2^{m+t}$ requires $t\ge m-1$ for $m\ge2$, by counting nonzero
pair differences. Thus A3 does not settle $t=o(m)$.

**What survives:** simultaneous isotropy gives a space of dimension at least
$\lceil m/(t+1)\rceil$ on whose cosets every quadratic coordinate is affine.
The uniform graph distribution is an exact mixture of affine sources of that
dimension. This is useful when $t=o(m/\log m)$; see [P1](proofs.md#p1-cheap-quadratic-graphs-can-be-sidon).
The [polynomial-source extractor literature](https://eccc.weizmann.ac.il/report/2023/140/revision/1/download/)
has obstructions around deficiency $N/\log N$; those do not establish the same
total-gate bound as A3. The circuit-restricted intermediate regime remains open here.

### A5. Large low-degree fibers are automatically usable product sources

**Refuted as an inference.** A feasible fiber of $b$ degree-$D$ Boolean equations
has at least $2^{n-Db}$ points, by applying the Reed–Muller weight bound to its
indicator. Cardinality alone says neither that the fiber contains a large affine
flat nor that it contains a large product. A3 and A11 give geometric obstructions.

**What survives:** for quadratic graph coordinates and queries with joint polar
span dimension $a$, simultaneous isotropy supplies affine pieces of dimension
at least $\lceil n/(a+1)\rceil-b$. With the worst-case $a$ growing like $b$,
this estimate runs out around the square-root scale rather than the required
near-linear query scale. Repeatedly decomposing after each query is even more costly.

### A6. Small circuits have small interaction across some balanced coordinate cut

**Refuted in the sublinear-interaction form.** For a bounded-degree expander $G$,
$f(x)=\sum_{uv\in E(G)}x_ux_v$ has linear size and logarithmic depth. Every
balanced raw-coordinate cut has mixed rank $\Omega(n)$: crossing edges contain
a linear-size induced matching. See [the proof](proofs.md#p2-large-interaction-does-not-imply-many-gates).

**What survives:** fixed-cut rectangle bounds with separately tracked side losses
are valid. The example does not exclude a favorable general linear coordinate
change or a target-specific constant-fraction interaction bound.

### A7. Choose a favorable linear basis independently for each query block

**Open bridge; not a free operation in the proof.** One scalar quadratic form
admits a nearly balanced split with zero mixed form, by grouping symplectic
blocks. This repairs A6 algebraically. A single split need not simplify a whole
vector of queries: the polar map in A3 has full joint mixed rank across every
nontrivial complementary split. Choosing a fresh basis also changes the geometry
of the surviving conditioned source.

**What survives:** classical canonical forms for pairs of alternating forms give
small simultaneous cross-rank layouts; there is no analogous universal
constant-rank conclusion for arbitrary triples. See [the pair/triple distinction](proofs.md#p2-large-interaction-does-not-imply-many-gates).
Neither favorable pairwise bases nor a hard triple supplies the missing total
cost of successive changes; the hard-triple existence argument does not give
linear-size circuits for those triples.

### A8. An invertible change of coordinates preserves product structure for free

**Refuted.** Start with independent $x\in\mathbb F_2^m$ and $y\in H$, where
$H$ has codimension $t$. Under $u=x$, $v=x+y$, the support becomes
$\{(u,v):u+v\in H\}$. Its entropy is unchanged, but the largest contained
product has total entropy smaller by $t$.

**What survives:** for affine support $S\le L\oplus R$, the exact loss is
$\dim\pi_LS+\dim\pi_RS-\dim S$. Keeping a mixture instead of one rectangle
retains a shared label of that dimension; the label is not free. A basis change
used to exhibit a sumset need not be implemented by gates, but its effect on
conditioning must still be included.

### A9. Reusing the same helpers or the same two cuts pays conditioning only once

**Refuted for arbitrary changing linear cuts.** If $H$ is the equation row space
and $P$ a cut projection, exact affine product restoration replaces it by
$H+HP$. Alternation with $Q$ can generate $HPQ$, $HQP$, and longer words.
Two fixed cheap projections can expand one initial equation to the full dual
space, losing $n-1$ additional bits without new helper values.
See [the closure example](proofs.md#p3-cut-changes-generate-new-equations).

**What survives:** one invariant equation space, or a proved small closure under
all selected projections, makes reuse safe. The counterexample does not rule out
the existence of a better, circuit-dependent choice of cuts.

### A10. Nested, chronological, circuit-derived cuts automatically have low total cost

**Refuted.** For prefix parities $p_i=x_1+\cdots+x_i$, start by conditioning
$p_n=0$ and restore products through successive prefix cuts. The equation rank
after $t$ restorations is $t+1$. These cuts are nested and follow an actual
linear-size computation, yet the accumulated loss is linear. Fixing all actual
prefix boundary values correctly pays that rank; it does not eliminate it.

**What survives:** compatible network partitions prevent *unaccounted* closure.
They do not prove that the accounted-for joint rank is small. Affine cut repair
can preserve the support without new restrictions, but the repaired cut need
not follow the circuit and may increase interaction rank.

### A11. Cheap causal sketches have fibers that split into small independent blocks

**Refuted, even at entropy rate tending to one.** There is a matrix with
$r=\lceil n/\log\log n\rceil$ rows, at most $3n$ nonzeros, and row weights
$O(\log n)$ whose kernel has dimension at least $n-r$ and distance
$\Omega(n/(\log\log n)^3)$. Its sketch is computed by linear-size shallow XOR
circuits. Every product contained in its zero fiber, over coordinate blocks
smaller than the distance, is a singleton: varying one factor would produce a
codeword below the distance. See [the proof](proofs.md#p4-cheap-high-entropy-fibers-can-resist-segmentation).

**What survives:** a theorem for a more restricted source family may be possible.
This fiber has density $2^{-o(n)}$, not constant density, so the example does not
refute a theorem confined to constant-density accepted sets. Linear causal
messages do have sparse row-space bases; arbitrary nonlinear messages need not.

## B. Charging computation instead of persistent information

### B1. Sum widths, ranks, or entropy over many cuts to get gate count

**Refuted as an accounting rule.** The same signal can remain available at many
boundaries. Its repeated presence is not repeated computation. Even satisfying
every two-sided rank demand

$$
w(P)\ge \operatorname{rank}M[Y,X^c]+
\operatorname{rank}M[Y^c,X]
$$

does not force superlinear graph size: linear-size logarithmic-depth
superconcentrators meet all corresponding dimension bounds simultaneously.
See [the graph argument](proofs.md#p5-all-rank-cut-demands-fit-a-small-graph).

**What survives:** these inequalities prove real capacity requirements. They
must be paired with an upper bound that accounts for reuse or a restriction on
the allowed graph/model.

### B2. Quadratic cumulative frontier entropy forces superlinear size

**Refuted for the proposed code targets.** For $F(x)=G^{\mathsf T}x$, where
$G$ generates an $[n,m,d]$ binary code, a chronological fan-in-two evaluation
satisfies

$$
\sum_{t=0}^{s-1}H(Z_t)\ge m\lfloor(d-1)/2\rfloor.
$$

Good-code parameters give $\Omega(n^2)$. But some such codes have linear-size
XOR encoders, and transposition gives linear-size logarithmic-depth circuits
for $F$ itself. See [the proof and model conventions](proofs.md#p6-quadratic-cumulative-information-with-linear-size).

**What survives:** the cumulative-information lower bound and the tradeoff
$s\max_t|Z_t|=\Omega(n^2)$ are unconditional in the stated evaluation model.
Not every good code is shown easy; code distance alone cannot give the stronger
size conclusion.

### B3. Force repeated increases of an affine-linearization potential

**Insufficient without compulsory forgetting.** Let $\lambda(Z)$ be the least
codimension of an affine subspace on which all retained signals are affine.
An AND gate raises it by at most one; deletion cannot raise it. These are valid
gate charges. But retaining the entire history makes $\lambda$ monotone and
bounded by $n$, so its total growth is at most $n$.

**What survives:** $\lambda$ proves a linear multiplicative-complexity bound and
can locate nonlinear work in a sketch. A repeated-charge argument needs a reason
why later demands require new nonlinear work even with the old signals present.

### B4. Many individually hard, jointly independent outputs require additive work

**Refuted.** For $n=2r+1$, let $y_i=x_i+x_n$,
$g=\sum_{j=1}^r y_{2j-1}y_{2j}$, and $F_i=x_i+g$. The map $F$ is an
involution, so its outputs on uniform input are jointly uniform. Each coordinate
has affine-linearization cost $r$, but all outputs together use only $r$ ANDs
and $3n-3$ binary gates. Their nonlinear core is shared; $F_i+F_j=x_i+x_j$.
See [the derivation](proofs.md#p7-independent-outputs-can-share-one-nonlinear-core).

**What survives:** hardness of *every nonzero output combination* detects this
example. Independence of output values is not independence of computational work.

### B5. Hardness of every output combination yields a superlinear bound

**Insufficient at the available scale.** If every nonzero combination of $m$
outputs has linearization cost at least $d$, cancellation of the last $m-1$
AND coefficients yields $b\ge m+d-1$ AND gates. More generally the output
subspace profile gives $b\ge\max_r(m-r+\delta_r)$.
Since $\delta_r\le n$, this particular criterion never exceeds $n+m-1$.

**What survives:** a legitimate vector-valued linear bound, related to
[Boyar–Find](https://arxiv.org/abs/1407.6169). In deep circuits one must retain
the entire ancestor prefix after cancellation; simply counting the remaining
nonzero coefficients would be invalid.

### B6. Apply a fresh-gate affine-disperser certificate in every segment

**Restricted result, with a saturation obstruction.** A segment whose incoming
signals are affine on a $D$-dimensional subspace can require fresh AND gates if
its output combinations stay hard there. But if a previously computed
dimension-$k$ affine disperser lies in the incoming affine span, every such
subspace has $D\le k$: an affine function on a space of dimension $k+1$ has a
constant hyperplane of dimension $k$.

**What survives:** fresh-gate bounds add over disjoint segments *when their relative
hardness hypotheses are proved*. The proposed iteration requiring $D>k$ cannot
be justified by retaining earlier dispersed outputs in the analysis history.

## C. Compilation and model-transfer gaps

### C1. Logarithmic depth implies a linear-time sublinear-workspace evaluation

**Refuted as a universal compiler claim.** B2 rules this out for fixed
chronological evaluations of the code-transpose targets. The
[Bazzi–Mitter encoder tradeoff](https://mitter.lids.mit.edu/publications/107_encoding_complexity_IEEE.pdf)
provides another benchmark: good codes cannot have both linear-time and
sublinear-workspace encoders in their branching-program model.

**What survives:** depth constrains dependency chains, not total live information.
Recomputation may save space but costs time. Read-only input access, write-only
outputs, and any readable output storage must be specified separately.

### C2. Treat an undirected frontier sweep as a deterministic small-space machine

**Invalid transfer.** A sweep may guess values before their producers are visited
and check consistency later. The compiled acceptor is nondeterministic (and
unambiguous for the circuit trace), not automatically a forward evaluator.
Small-space regularity/crossing-sequence theorems also depend on input-head,
uniformity, and space conventions absent from this nonuniform network model.

**What survives:** trace fixing and splicing are genuine analogies. The analogy
to the user's small-space “trace method” did not establish a size-preserving
simulation or identify an applicable regularity theorem. It must not be used as
a proof that circuit segments collapse to zero-space computation.

### C3. Compile to formulas or bounded-width branching programs and transfer hardness

**Insufficient quantitative control.** Unfolding shared subcircuits can duplicate
large ancestor cones. Barrington's bounded-width simulation preserves polynomial
size for logarithmic-depth formulas, not the near-linear gate budget needed here.
A lower bound in the compiled model can be consumed by this simulation overhead.

**What survives:** useful restricted-model bounds and possible alternative targets.
Every claimed transfer must specify the blowup as a function of the original
size and depth; bounded width alone is not a sufficient guarantee.

### C4. Bound arbitrary local or quadratic query count directly above $n$

**Insufficient.** Reading the $n$ raw input bits computes any Boolean function
when arbitrary decoding is free. Hence a model permitting raw-bit queries has
an $n$-query upper bound. A useful hybrid instead needs an $\Omega(n)$ query
lower bound *and* a compiler using $o(s)$ queries, while preserving the relevant
support or interaction restrictions. No such new compiler was proved here.

**What survives:** fixed-support majority-rectangle arguments and separated side
entropy budgets. Repeated or determined queries cost nothing, but arbitrary
local functions can hide substantial computation that the relaxation discards.

### C5. Treat linear outputs as evidence that all intermediate messages are linear

**Unproved hypothesis.** For linear broadcasts, a target $Mx$ with local supports
$T_i$ has optimum message length
$\min_{D:\operatorname{supp}D_i\subseteq T_i}\operatorname{rank}(M-D)$.
The kernel argument proving this does allow nonlinear *decoders*, but assumes a
linear *broadcast*. A linear target does not impose that assumption on its circuit.

**What survives:** a connection to [systematic linear data structures and rigidity](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2020.35).
[Nonlinear index coding](https://arxiv.org/abs/0806.1919) prevents a blanket
replacement of nonlinear broadcasts by linear ones. Those separations alone do
not resolve the special sparse-support instances needed here.

### C6. Transfer large-field or restricted arithmetic lower bounds to Boolean gates

**Invalid without a cost-preserving encoding.** Totally regular square matrices
of dimension at least two do not exist over $\mathbb F_2$: nonzero entries would
all equal one. Large-field symbols can carry many bits; a field-operation count
is not a Boolean gate count. Bounded-coefficient and unitary arithmetic arguments
also impose hypotheses absent from arbitrary Boolean circuits.

**What survives:** genuine field-symbol results and methodological examples, such
as [Ailon's per-operation matrix-entropy potential](https://arxiv.org/abs/1305.4745).
An encoding or simulation must pay for arithmetic and preserve the restrictions
before its lower bound can be imported.

## D. Multi-output shared sketches

### D1. The shared-sketch abstraction itself supplies a new lower bound

**Open bridge in an established model.** The representation
$F_i(x)=g_i(x_{T_i},H(x))$ is Valiant's common-bits model. It forgets the cost
of producing $H$ and the decoders. For a single output it is vacuous: transmit
that output in one bit. With many outputs it becomes a genuine hard problem,
not a completed proof. See [Corrigan-Gibbs–Kogan](https://eccc.weizmann.ac.il/report/2018/182/download).

**What survives:** for fixed $\epsilon>0$, excluding
$q=O(n/\log\log n)$ and $\ell=n^\epsilon$ for an explicit operator would
exclude linear-size logarithmic-depth circuits. Causal sketches retain additional
equations $Z_j=\phi_j(X_{S_j},Z_{<j})$, but A11 shows locality alone is not enough.

### D2. One union-of-probes entropy bound handles all receivers

**Insufficient at the generic parameter scale.** The valid inequality
$q\ge H(F_J(X)\mid X_{\cup_{j\in J}T_j})$ allows nonlinear sketches.
Using only $|\cup T_j|\le |J|\ell$ gives a guarantee of order $n/\ell$ in
the full-rank field example, far below $n/\log\log n$ for polynomial $\ell$.

**What survives:** exploit substantial probe overlap or stronger joint receiver
constraints. This is not an upper bound on the true broadcast complexity or on
what the inequality proves for special support patterns.

### D3. Apply the query-with-sketch min-entropy argument to a large output batch

**Insufficient through the naive reduction.** A $q$-bit sketch can be fixed and
union-bounded over its values. To contradict it using $k$ output bits needs a
conditional output entropy greater than $q$, hence $k>q$. Independently decoding
those outputs uses up to $k\ell$ raw probes. At
$q\asymp n/\log\log n$ and $\ell=n^\epsilon$, that upper bound exceeds $n$;
the required guarantee would include revealing the entire input.

**What survives:** refined probe accounting, carefully chosen batches, or the
actual shared residual DAG. This is a parameter failure of this application,
not a limitation theorem for the entire query-with-sketch framework.

### D4. Sequential entropy increments and the acyclic-set bound reach the target

**Insufficient in general.** The valid strengthened inequality is

$$
q\ge\sum_t H(F_{i_t}(X)\mid X_{\cup_{u\le t}T_{i_u}},F_{i_1}(X),\ldots,F_{i_{t-1}}(X)).
$$

For coordinate demands its optimum over orders is the maximum acyclic induced
subgraph bound from index coding. There are degree-$\ell$ support patterns for
which it is $O(n\log n/\ell)$ for *every* cyclic shift. A union bound over
ordered vertex subsets proves this; see [the argument](proofs.md#p8-a-limit-of-sequential-entropy).

**What survives:** stronger index-coding inequalities or circuit-specific support
structure. These random support patterns have not been compiled into linear-size
circuits, and they do not bound the true index-coding optimum from above.

### D5. Prove a shift lower bound after optimizing the wiring for each shift

**Refuted by a trivial decoder.** For fixed shift $p$, choose
$T_i=\{i+p\pmod n\}$; no broadcast is needed. The useful quantifiers require
one wiring pattern chosen before the shift, followed by a hard shift for that
pattern. Allowing the broadcast and decoder functions to vary with $p$ is a
separate, legitimate relaxation.

**What survives:** the fixed-wiring parameterized-shift problem. The elementary
acyclic-set guarantee $(n-\ell)/(\ell+1)$ remains too weak in the desired regime.

### D6. More outputs or more full-rank cuts automatically add gate demand

**Refuted as an automatic consequence.** Multi-output splicing is valid without
a bound on output count. Rectangular maps can require large frontiers throughout
an interval of cuts. But B1's superconcentrators meet all maximal rank demands
with only $O(n+m)$ edges; additional cuts need not require additional gates.

**What survives:** mixed input-output recovery and stronger restricted layout
bounds. The issue is an additive cost theorem for computation between cuts,
not a failure of the multi-output cut lemma itself.

## E. Literature barriers and the current unfinished route

### E1. Strong multiscale entropy bypasses the reuse problem by itself

**Refuted for that specific criterion.**
[Drucker's CCC 2012 paper](https://people.csail.mit.edu/andyd/arbgates_11p.pdf)
constructs operators with enhanced Strong Multiscale Entropy and very cheap
arbitrary-gate wire implementations. The demands at different scales can
describe different choices of a replicated block, rather than additive work
on one execution. Its depth-two/depth-three separation also obstructs a naive
iteration of [Jukna's operator-entropy method](https://web.vu.lt/mif/s.jukna/ftp/entropy-sub.pdf).

**What survives:** target-specific structure beyond those entropy properties.
This is not a barrier to every information-theoretic method, and arbitrary-gate
wire upper bounds are not automatically binary-gate upper bounds.

### E2. Turn coded information into separately routed messages

**External conditional route, not an available unconditional lemma.**
[Afshani–Freksen–Kamma–Larsen](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2019.10)
derive multiplication and shift lower bounds assuming the undirected
multiple-unicast conjecture. October 2026 preprints by
[Braverman–He](https://arxiv.org/abs/2610.10108) and
[Li–Li–Liu](https://arxiv.org/abs/2610.20079) report counterexamples to that
conjecture. Their certificates were not independently audited in this exploration.

**What survives:** the published conditional implication, and possible routing
arguments for specially justified network classes. Neither the conjecture nor
a rule forbidding coding gains can be silently assumed in a circuit compiler.

### E3. High marginal entropy makes conditioned sources nearly independent

**Refuted.** If $A,B$ are independent uniform $r$-bit strings and
$Z=A_1+B_1$, both conditional marginals remain uniform, but
$I(A;B\mid Z)=1$. An extractor's independence hypothesis is not supplied by
retaining marginal min-entropy. A small number of equations need not mean
negligible conditional correlation.

**What survives:** quantitative decoupling. For average conditional min-entropies
$k_A,k_B$ and any sign predictor $g(Z)$,

$$
|\mathbb E[g(Z)(-1)^{\langle A,B\rangle}]|
\le 2^{(r-k_A-k_B)/2}+\sqrt{2\ln(2)I(A;B\mid Z)}.
$$

This follows by comparison with the product of the conditional marginals and
Pinsker's inequality; it is closely related to [Ko, Lemma 3.10](https://arxiv.org/html/2509.02730v1).
It supplies an extraction ingredient, not yet a circuit cost theorem.

### E4. Amortize conditional correlation over arbitrary actual cuts

**Open bridge; the naive sum is false.** A single global parity $P$ gives
$I(X_S;X_{S^c}\mid P)=1$ for every nontrivial coordinate cut of uniform input.
Summing over $n-1$ nested cuts charges this same one-bit transcript $n-1$ times.
The actual shallow circuit computing $P$ and then $Y_i=P+x_i$ can reuse $P$
at every output step. See [the accounting distinction](proofs.md#p9-what-conditional-correlation-does-and-does-not-amortize).

**What survives:** for one fixed binary hierarchy of input blocks and one common
transcript, sibling conditional mutual informations telescope to total
correlation, at most the transcript entropy for initially independent blocks.
This does not apply to arbitrary moving bipartitions or different transcripts
at different nodes. Such a budget also saturates at the input entropy. Deriving
fresh, target-dependent gate charges beyond it remains unfinished.

## What has not failed

The following remain valid or genuinely open, rather than being disproved by
the examples above:

- The repository's existing frontier and multi-output splicing theorems.
- Exact compatible-partition gluing and joint-rank accounting for affine signals.
- Fixed-cut interaction/rectangle bounds, including conditional response profiles.
- The high-rate quadratic affine-source decomposition in its stated regime.
- Conditional fresh-AND lower bounds for segments satisfying relative hardness.
- Unconditional size–space and cumulative-information bounds for code transposes.
- Target-specific common-bits lower bounds, and refinements retaining causal
  production of shared bits and the cost of the residual circuit.
- Quantitative conditional decoupling, provided entropy loss and correlation
  are established together with a nonduplicating gate charge.

The recurring missing theorem is a **supply theorem**: small circuits must admit
a useful representation with a controlled *joint* cost, and the target must remain
hard in that representation. Individual cut demand, output independence, and
retained entropy do not supply that theorem on their own.
