# Proofs and model checks for the failure catalogue

Authors: Christian Reitwiessner

This companion to the [catalogue](README.md) supplies the main counterexamples
and accounting arguments in a form independent of the exploratory scratch work.
These are paper proofs, not Lean-checked results. No claim of priority or new
unrestricted superlinear circuit lower bound is made. Literature inputs are
identified where used; the deductions and their limitations are stated here.

All vector spaces below are over $\mathbb F_2$, except when a field extension is
explicitly introduced. Entropy is in bits. Binary circuit constructions count
both XOR and AND gates, with unrestricted fan-out; multiplicative complexity
counts only AND gates. Constants in asymptotic notation are independent of input
length.

## P1. Cheap quadratic graphs can be Sidon

**Claim.** There are quadratic maps $P:\mathbb F_2^m\to\mathbb F_2^{O(m)}$
computed by $O(m)$ binary gates at depth $O(\log m)$ whose graphs contain no
$A+B$ with $|A|\ge3$ and $|B|\ge2$.

[Spielman's linear-time encodable codes](https://www.cs.yale.edu/homes/spielman/PAPERS/linearTimeIT.pdf)
supply a binary linear encoder $C:\mathbb F_2^m\to\mathbb F_2^L$, with
$L=O(m)$, relative distance at least a constant $\delta>0$, and a linear-size,
logarithmic-depth encoding circuit. Fix $\epsilon<1/3$. Take a constant-degree
bipartite graph with $L$ vertices on each side such that every left set of size
at least $\delta L$ has neighbors at more than $(1-\epsilon)L$ right vertices.
Such graphs exist by a union bound over pairs of sets with no edge between them,
or by taking a sufficiently large constant power of a spectral expander.

For each right vertex $i$, let $E_i(x)\in\mathbb F_2^a$ be the tuple of
codeword coordinates at its neighbors, where $a$ is the constant degree. Then
every nonzero $x$ has fewer than $\epsilon L$ zero tuples. Copying the encoder's
wires produces all tuples without further gates. Define

$$
P(x)_{i,j,k}=E_i(x)_j E_i(x)_k,\qquad j<k.
$$

There are $L\binom a2=O(m)$ additional AND gates, in one layer. For independent
directions $u,v$, the three words $u,v,u+v$ are nonzero. Outside the union of
their zero-tuple sets, $E_i(u)$ and $E_i(v)$ are nonzero and distinct, hence
linearly independent over $\mathbb F_2$. Some two-by-two minor is nonzero.
Consequently the polar map

$$
B(u,v)=P(u+v)+P(u)+P(v)
$$

is nonzero for every independent pair $u,v$.

For $v\ne0$, equality $P(x+v)+P(x)=P(y+v)+P(y)$ is equivalent to
$B(v,x+y)=0$. Thus $y=x$ or $y=x+v$. Every nonzero difference of graph points
has at most one representation as an unordered pair of distinct graph points:
the graph is Sidon. If $A+B$ lies in this graph, choose distinct $b_0,b_1\in B$.
All pairs $\{a+b_0,a+b_1\}$ have difference $b_0+b_1$ and must be the same
unordered pair. At most two choices of $a$ produce that pair, proving the claim.

An exact mixture of sumset distributions with both component min-entropies
greater than one is likewise impossible: every positive-weight mixture component
would have to be supported inside the graph. This does not estimate distance
from approximate mixtures. Counting pair differences gives

$$
\binom{2^m}{2}\le 2^{m+t}-1
$$

for a Sidon graph with $t$ output coordinates. For $m\ge2$, this requires
$t\ge m-1$. Thus this obstruction does not settle the high-rate regime $t=o(m)$.

**A positive high-rate statement.** For any $t$ alternating polar forms on
$\mathbb F_2^m$, take a maximal common totally isotropic subspace $W$, of
dimension $r$. Its common orthogonal space has dimension at least $m-tr$.
It equals $W$: otherwise one could append another direction while preserving
isotropy, because the forms are alternating. Therefore
$r\ge\lceil m/(t+1)\rceil$. Each quadratic coordinate is affine on every
coset of $W$, so the uniform graph distribution is an exact mixture of affine
sources of dimension $r$.

More generally, use the dimension of the joint polar-form span in place of
$t$. Imposing $b$ further quadratic queries whose polar forms lie in that span
costs at most $b$ dimensions on any such coset with a feasible answer. This
justifies the catalogue's affine-piece estimate; it does not yield large pieces
when the polar span itself grows too quickly. The different high-entropy
obstructions in [Extractors for Polynomial Sources over $\mathbb F_2$](https://eccc.weizmann.ac.il/report/2023/140/revision/1/download/)
should not be assigned the linear total-gate bound proved above.

## P2. Large interaction does not imply many gates

Let $G$ be a bounded-degree edge expander on $n$ vertices, of maximum degree
$\Delta=O(1)$, and put

$$
f_G(x)=\sum_{uv\in E(G)}x_ux_v.
$$

There are $O(n)$ products and a balanced XOR tree, giving $O(n)$ binary gates
and $O(\log n)$ depth. Across any balanced coordinate cut $L\mid R$, expansion
gives $\Omega(n)$ crossing edges. In a bipartite graph of maximum degree
$\Delta$, greedy selection finds an induced matching of size at least
$|E|/(2\Delta^2)$: selecting an edge and deleting edges incident to either
endpoint's neighbors removes at most $2\Delta^2$ edges. The corresponding
submatrix of the crossing adjacency matrix $M$ is an identity matrix. Hence
$\operatorname{rank}M=\Omega(n)$ over $\mathbb F_2$.

This is meaningful interaction. Write the function across the cut as
$u(x_L)+v(x_R)+x_L^{\mathsf T}Mx_R$. If it is constant on a rectangle
$A\times B$, taking four corners shows that the direction spans
$U=\operatorname{span}(A-A)$ and $V=\operatorname{span}(B-B)$ obey
$U^{\mathsf T}MV=0$. If $M$ has rank $r$, rank-nullity gives
$\dim U+\dim V\le n-r$, and thus

$$
|A|\,|B|\le 2^{n-r}.
$$

Nevertheless the function has linear-size circuits. This refutes a universal
sublinear mixed-rank or sublinear rectangle-loss guarantee for balanced
*coordinate* cuts. It does not refute every constant-factor guarantee. A general
linear change of basis can put a scalar alternating form into symplectic blocks;
grouping whole blocks gives a nearly balanced split with zero mixed form.
Applying a different basis after conditioning must also pay for its effect on
the surviving source, as P3 shows.

**Pairs and triples behave differently.** The canonical form for a pair of
alternating forms, including characteristic two, has regular blocks with
off-diagonal matrices $I,C$, where $C$ is a companion matrix, and singular
blocks with off-diagonal matrices $[I\ 0],[0\ I]$. See
[Waterhouse, pp. 281–282](https://msp.org/pjm/1977/69-1/pjm-v69-n1-p21-s.pdf).
In a regular block, order the coordinates $x_1,y_1,x_2,y_2,\ldots$. At every
prefix cut, the companion shift and identity contribute at most one crossing
edge between them; the companion's last column contributes a rank-one star.
The joint left and right mixed ranks are therefore at most two. A singular
block has a path ordering with rank at most one. Concatenating the block orders
gives this bound at every prefix cut, hence at a balanced cut.

For contrast, choose three independent uniform alternating forms in dimension
$2m$. At any fixed ordered balanced decomposition $U\oplus V$, their mixed
matrices $M_1,M_2,M_3$ are independent uniform $m\times m$ matrices. The
probability that their joint column span has dimension at most $r$ is at most

$$
4\cdot2^{r(m-r)}\,2^{-3m(m-r)}
=4\cdot2^{-(3m-r)(m-r)}.
$$

Here $4\cdot2^{r(m-r)}$ bounds the number of $r$-dimensional subspaces.
There are at most $4\cdot2^{2m^2}$ ordered balanced decompositions: choose
one side and then a complement. For $r=\lfloor m/4\rfloor$, the union bound
over all decompositions is at most $16\cdot2^{-m^2/16}$, tending to zero.
Thus triples exist with joint mixed rank greater than $\lfloor m/4\rfloor$ at
every balanced linear split. Swapping the ordered sides gives the same
conclusion for row rank. This existence proof supplies neither cheap circuits
for those triples nor the needed extractor hardness. The positive result for
pairs supplies no bound on the cost of switching between their favorable bases.

## P3. Cut changes generate new equations

A linear cut is an idempotent projection $P$ with image $U$ and kernel $V$.
For a linear support $S$, the largest direction space of a product inside an
affine translate of $S$ is

$$
R_P(S)=(S\cap U)\oplus(S\cap V)=S\cap P^{-1}(S).
$$

Indeed, $s,Ps\in S$ exactly when both components of $s$ belong to $S$.
Differences within either side of any contained rectangle lie in the respective
intersection, even if the sides are not affine. A translate of $R_P(S)$ attains
the maximum cardinality. If $H=S^\perp$ is the equation row space, the dual
update is

$$
R_P(S)^\perp=H+HP.
$$

Thus repeating one cut is free after the first restoration, but switching to
$Q$ may add $HQ$, $HPQ$, and eventually longer words. Total loss is bounded
by the dimension of the span of all such words minus $\dim H$. A common
invariant equation space supplies a valid compatibility condition; merely
counting different helper values or different projections does not.

**Two cheap projections with full closure.** Let $K=\mathbb F_{2^m}$, $m\ge2$,
and choose $\alpha$ of degree $m$ over $\mathbb F_2$. On $K^2$ define

$$
P(x,y)=(x,0),\qquad
Q(x,y)=(\alpha x+y,(1+\alpha)(\alpha x+y)).
$$

Both maps are idempotent of binary rank $m$. A $P$-invariant subspace has form
$X\times Y$. Its invariance under $Q$ implies

$$
\alpha X\subseteq X,\quad Y\subseteq X,\quad
\alpha(1+\alpha)X\subseteq Y,\quad (1+\alpha)Y\subseteq Y.
$$

The last inclusion also gives $\alpha Y\subseteq Y$. Because
$\mathbb F_2[\alpha]=K$, each of $X,Y$ is either $0$ or $K$. The other
inclusions force them both to be $0$ or both to be $K$. There is no nonzero
proper common invariant subspace.

Starting with any hyperplane $S$ and alternating maximal restorations for $P$
and $Q$ therefore ends at zero: the descending sequence stabilizes at a common
invariant subspace contained in $S$. One initial equation generates a full
$2m$-dimensional equation space, losing $2m-1$ additional bits. In a polynomial
basis, multiplication by $\alpha$ is a shift with fixed feedback, using $O(m)$
XORs and constant depth. The $Q$-coordinates
$u=\alpha x+y$, $v=(1+\alpha)x+y=u+x$ are cheap and may be retained throughout.
No new helper values need to be produced when the proof revisits these cuts.
This example concerns arbitrary cut sequences, not the nonexistence of a good
circuit-dependent sequence.

**Nested coordinate cuts also accumulate loss.** Start with the equation
$p_n=x_1+\cdots+x_n=0$. Restoring products across prefix cuts after coordinates
$1,2,\ldots,t$ gives the equation space spanned by

$$
e_1,\ldots,e_t,\ e_{t+1}+\cdots+e_n,
\qquad 0\le t\le n-1.
$$

Its rank is $t+1$. The cuts follow the linear-size prefix-parity computation,
but their joint information cost grows linearly. Correctly fixing all boundary
values accounts for this growth; it does not remove it.

**Exact loss under a basis change.** For $S\le L\oplus R$, rank-nullity yields

$$
\dim S-\dim R_P(S)=\dim\pi_LS+\dim\pi_RS-\dim S.
$$

For independent $x\in\mathbb F_2^m$ and $y\in H$ with $H$ of codimension
$t$, the shear $(x,y)\mapsto(u,v)=(x,x+y)$ produces support
$u+v\in H$. Both projections have dimension $m$ while the support has
dimension $2m-t$, so the largest product loses exactly $t$ bits.

## P4. Cheap high-entropy fibers can resist segmentation

Set $r=\lceil n/\log\log n\rceil$ for sufficiently large $n$. There exists
an $r\times n$ matrix $A$ with at most $3n$ nonzeros, row weights $O(\log n)$,
and

$$
\dim\ker A\ge n-r,\qquad
d(\ker A)=\Omega(r^3/n^2)=\Omega(n/(\log\log n)^3).
$$

Here is a probabilistic existence proof. For each column independently, choose
three uniform row positions with replacement and add their indicators modulo
two. A fixed set of $t$ columns sums to zero only if all $3t$ samples have even
multiplicity. This is impossible for odd $t$. For even $t$, a union bound over
pairings bounds its probability by

$$
(3t-1)!!\,r^{-3t/2}\le(3t/r)^{3t/2}.
$$

Union-bounding over the column sets gives

$$
\Pr[\text{a weight-}t\text{ codeword exists}]
\le \left(Cn\sqrt t/r^{3/2}\right)^t,
\qquad C=e\,3^{3/2}.
$$

Choose $c>0$ so that $C\sqrt c\le1/4$. Summing over even
$2\le t\le\lfloor cr^3/n^2\rfloor$ gives at most
$\sum_{j\ge1}4^{-2j}=1/15$. Each row's load before cancellation is binomial
with mean $3n/r=O(\log\log n)$. A tail bound and union bound give maximum
load $O(\log n)$ with probability tending to one. Thus the desired properties
hold simultaneously with positive probability. The dimension bound follows
from having at most $r$ independent equations.

Independent balanced parity trees compute $Ax$ using at most $3n$ XOR gates
at depth $O(\log\log n)$. Its zero fiber has entropy at least $n-r$. Yet any
product inside this fiber over disjoint coordinate blocks smaller than
$d(\ker A)$ is a singleton: varying one factor while fixing all others would
produce a nonzero kernel vector supported on that one block. This includes
blocks of size $n^\epsilon$ for any fixed $0<\epsilon<1$ and sufficiently
large $n$.

The fiber density is $2^{-\operatorname{rank}A}\ge2^{-r}$ and tends to zero:
distance at least three forces the columns to be distinct and nonzero, so
$2^{\operatorname{rank}A}\ge n+1$. The example does not refute a claim restricted
to constant-density accepted sets. Nor is this random existence argument an explicit hard-function
construction. It refutes an automatic product decomposition even for cheap,
local, linear sketches of $o(n)$ bits.

## P5. All rank-cut demands fit a small graph

For an $m\times n$ matrix $M$ and a vertex cut containing input terminals
$X$ and output terminals $Y$, the two-direction rank demand is at most

$$
\operatorname{rank}M[Y,X^c]+\operatorname{rank}M[Y^c,X]
\le \min(|Y|,n-|X|)+\min(m-|Y|,|X|).
$$

A directed superconcentrator has vertex-disjoint paths from any chosen set of
input terminals to any equally sized set of output terminals, with the matching
chosen by the paths. Such graphs exist with linear size, bounded degree, and
logarithmic depth; see [Pippenger's construction](https://scholarship.claremont.edu/hmc_fac_pub/146/).
Use $N=\max(n,m)$ and select $n$ input and $m$ output terminals, treating any
unused terminals as internal vertices. This gives $O(n+m)$ size.

For any vertex cut, take paths from inside inputs to outside outputs, up to
the maximum possible number $\min(|X|,m-|Y|)$. They require that many distinct
outgoing crossing edges. Paths from outside inputs to inside outputs require
$\min(n-|X|,|Y|)$ distinct incoming crossing edges. The two path families need
not be disjoint from each other: outgoing and incoming crossing edges are
different sets. Thus the total crossing-edge count satisfies the displayed
bound for every cut simultaneously.

This is a graph-capacity counterexample, not a claim that one small circuit
computes every matrix. It shows that the entire family of these necessary
rank inequalities, even at maximal rank, cannot by itself force more than
linear graph size. A stronger argument must constrain the computation assigned
to the graph or the permitted graph class.

## P6. Quadratic cumulative information with linear size

Let $G$ be an $n\times m$ full-column-rank generator matrix of a binary code
of minimum distance $d\ge3$, and set $F(x)=G^{\mathsf T}x$. For every output
subset $J$ and every input-coordinate subset $T$ with $|T|<d$,

$$
\operatorname{rank}G^{\mathsf T}[J,T^c]=|J|,
\qquad H(F_J(X)\mid X_T)=|J|
$$

for uniform $X$. Otherwise a nonzero combination of the selected generator
columns would be a codeword supported inside $T$, contradicting distance.

**Evaluation model and cumulative bound.** Fix a topological order of a
fan-in-two circuit, evaluating one gate at each step. Raw inputs may be reread
for free when used as operands. Let $Z_t$ be the vector of computed internal
values needed after time $t$; take $Z_0$ empty. Emit each output as soon as it
is computed. Emitted outputs are write-only: any value needed by later gates
must remain in $Z_t$. The schedule is fixed independently of the input.

Put $L=\lfloor(d-1)/2\rfloor$. The next at most $L$ gates read at most
$2L<d$ raw input coordinates. If $J_t$ is the set of outputs emitted in that
window and $T_t$ its raw input accesses, those outputs are determined by
$(Z_t,X_{T_t})$. Hence

$$
|J_t|=H(F_{J_t}(X)\mid X_{T_t})\le H(Z_t).
$$

No output can occur in the first $L$ gates, by the same argument with empty
initial state. Each output emitted at step $p>L$ appears in exactly $L$ windows,
starting at $p-L,\ldots,p-1$. Therefore, for $s$ gates,

$$
\sum_{t=0}^{s-1}H(Z_t)\ge mL,
\qquad s\max_t |Z_t|\ge mL.
$$

For constant-rate, constant-relative-distance codes these are $\Omega(n^2)$
lower bounds on cumulative information and size times maximum live width.
They do not say that size alone is superlinear.

**Why some targets still have linear-size logarithmic-depth circuits.**
An XOR circuit computing $G$ can be transposed by propagating adjoint values
backward: each original vertex sums the adjoints of its successors, plus a new
input for each original output port there. The total number of summands is the
number of original edges plus output ports. Binary addition trees therefore
give size $O(S+n+m)$ from an original size-$S$ encoder. This is the linear
transposition principle; see [Bostan–Lecerf–Schost](https://specfun.inria.fr/bostan/publications/BoLeSc03.pdf).

The depth can also be controlled without assuming bounded original fan-out.
Let $p(v)$ be the integer number of paths from $v$ to the original output
ports, retaining only vertices with $p(v)>0$. Assign weights $p(u)$ to successor
adjoints and weight one to port injections, so their sum is $p(v)$. By the
binary prefix-code inequality, a summation tree can give a term of weight $w$
depth at most $\lceil\log_2(p(v)/w)\rceil$, with at most one fewer internal
gates than terms after suppressing unary vertices. Along a reversed path the
logarithms telescope. If the original depth is $D$ and it has $b$ output ports,
then $p(v)\le b2^D$, and the transposed depth is at most
$2D+\log_2 b+1$.

Apply this to the linear-size logarithmic-depth encoders used in P1. Their
transposes have the same asymptotic size and depth while satisfying the
quadratic cumulative-information bound. Thus good-code distance alone cannot
turn cumulative frontier entropy into a superlinear gate lower bound. This
does not assert that every good code has such an encoder. Different evaluation
models, especially readable output storage or input-dependent schedules, require
their own formulation rather than silently inheriting the proof above.

## P7. Independent outputs can share one nonlinear core

For $n=2r+1$, $r\ge1$, define

$$
y_i=x_i+x_n\ (1\le i\le2r),\qquad
g(x)=\sum_{j=1}^r y_{2j-1}y_{2j},\qquad F_i(x)=x_i+g(x).
$$

Adding the all-ones vector leaves each $y_i$ unchanged. Thus $g(F(x))=g(x)$,
and $F(F(x))=x$. Uniform inputs give jointly independent uniform outputs.
The polar form of $g$ has rank $2r$; its maximal isotropic dimension is $r+1$.
Consequently the least codimension $\lambda(F_i)$ of a nonempty affine space
on which $F_i$ becomes affine is exactly $r$. This is attained by fixing one
coordinate from each displayed pair of $y$'s.

Nevertheless all outputs use only $r$ AND gates and $6r=3n-3$ total binary
gates: $2r$ XORs for the $y_i$, $r$ products, $r-1$ XORs to sum them, and $n$
final XORs. Depth is logarithmic. The nonlinear work is the same for every
output, as $F_i+F_j=x_i+x_j$.

**What cancellation does prove.** Suppose every nonzero combination of $m$
outputs has $\lambda\ge d\ge1$. With AND gates $z_1,\ldots,z_b$ in
topological order, write

$$
F_i=a_i(x)+\sum_{j=1}^b R_{ij}z_j,
$$

where $a_i$ is affine. The matrix $R$ must have row rank $m$, since otherwise
a nonzero output combination is affine. Choose a nonzero combination cancelling
the last $m-1$ columns of $R$. It is computable using the first $b-m+1$ AND
gates and free affine operations. Successively fixing one nonconstant affine
operand of each AND gate makes the whole prefix affine at codimension at most
$b-m+1$. Thus

$$
b\ge m+d-1.
$$

One must keep that entire ancestor prefix; merely counting the nonzero remaining
output coefficients would be invalid for deep circuits. For an $m$-dimensional
output space $V$ modulo affine functions, define
$\delta_r(V)=\min_{W\le V,\ \dim W=r}\lambda(W)$, where linearization is
simultaneous. Cancelling the last $m-r$ coefficients gives an at least
$r$-dimensional space and proves

$$
b\ge\max_{1\le r\le m}\{m-r+\delta_r(V)\}.
$$

Because $\delta_r\le n$, this criterion has numerical ceiling $n+m-1$.
These are vector-valued multiplicative-complexity arguments, in the setting of
[Boyar–Find](https://arxiv.org/abs/1407.6169); they are not a superlinear bound.
Applied to an actual segment, the same argument counts fresh AND gates only
if the incoming signals are affine on a subspace where all the required output
combinations retain the asserted relative hardness.

## P8. A limit of sequential entropy

Let $Z=h(X)$ be a sketch of at most $q$ bits, and let
$Y_i=g_i(X_{T_i},Z)$ for fixed coordinate sets $T_i$. Relabel the outputs in
any chosen order and put $U_t=\bigcup_{i\le t}T_i$. Then

$$
\sum_t H(Y_t\mid X_{U_t},Y_{<t})\le H(Z)\le q.
$$

For a proof put $K_t=(X_{U_t},Y_{\le t})$ and
$D_t=U_t\setminus U_{t-1}$. Exact decoding and the chain rule give

$$
I(Z;K_t)-I(Z;K_{t-1})
=I(Z;X_{D_t}\mid K_{t-1})+H(Y_t\mid X_{U_t},Y_{<t}).
$$

The first term is nonnegative and the left side telescopes. No linearity of
the sketch or decoders, or independence of the input distribution, was needed.

For coordinate demands $Y_i=X_i$ on independent uniform bits, draw an edge
$i\to j$ when receiver $i$ knows $X_j$. Remove receivers that already know
their own bit. A receiver contributes one exactly when its demand is absent
from all revealed raw inputs and earlier outputs. In the contributing induced
subgraph, an edge can only point to an earlier contributing receiver, so that
subgraph is acyclic. Conversely, ordering an acyclic induced set so that all
its out-neighbors come earlier makes each of its vertices contribute one.
The optimum over orders is exactly the maximum acyclic induced subgraph bound
(MAIS) from [index coding](https://webee.technion.ac.il/people/zivby/papers/indexing/indexing.full.pdf).

**Why it can be too weak for every shift.** Fix $0<\epsilon<1$ and let
$\ell=n^\epsilon$. Choose each entry of an $n\times n$ side-information
matrix independently with probability $p=\ell/(2n)$, allowing diagonal
entries. With probability tending to one every row has at most $\ell$ entries.
For a fixed cyclic shift of demanded coordinates, entries remain independent
with the same distribution. An ordered $k$-tuple can be a topological ordering
only if $k(k-1)/2$ specified arcs are absent. A union bound over all tuples and
all shifts gives

$$
\Pr[\text{some shift has an acyclic set of size }k]
\le n\,n^k(1-p)^{k(k-1)/2}
\le\exp\bigl(\log n+k\log n-\ell k(k-1)/(4n)\bigr).
$$

With natural logarithms in this estimate and
$k=\lceil8n\log n/\ell\rceil+2$, the bound tends to zero. Ignoring loop
conditions only makes this upper bound larger; deleting self-informed receivers
cannot create a larger induced acyclic set. Thus some support patterns have
degree at most $\ell$ and MAIS $O(n\log n/\ell)$ for every shift. For
polynomial $\ell$, this is $o(n/\log\log n)$.

This is a limitation of the sequential/acyclic lower bound, not an upper bound
on actual broadcast complexity. The random supports have not been realized as
residual cones of linear-size circuits. Additional circuit structure or stronger
index-coding inequalities may change the conclusion.

## P9. What conditional correlation does and does not amortize

**One bit can correlate many different cuts.** Let $X_1,\ldots,X_n$ be
independent uniform bits and $P=X_1+\cdots+X_n$. For every nonempty proper
$S\subset[n]$, both conditional marginals $X_S\mid P$ and $X_{S^c}\mid P$
remain uniform, while $H(X\mid P)=n-1$. Therefore

$$
I(X_S;X_{S^c}\mid P)=1.
$$

Summing over $n-1$ nested prefix cuts gives $n-1$, although $H(P)=1$. The
same phenomenon occurs in an actual shallow circuit: compute $P$ by a balanced
XOR tree and then $Y_i=P+X_i$, using $2n-1$ gates and depth at most
$\lceil\log_2 n\rceil+1$. Once $P$ is available it can be reused for every
output. With read-only raw inputs and write-only emitted outputs, only $P$
needs to remain as internal state during that output phase. For even $n$ the
whole output map is an involution, so its outputs are jointly uniform as well.

These prefix partitions of raw inputs are not automatically complete graph
separators. The example refutes summing conditional mutual information over
moving input cuts with a budget of just $H(P)$; it does not refute exact
trace-gluing for genuine network partitions with every interface accounted for.

**A fixed hierarchy has an exact budget.** Let $X_1,\ldots,X_k$ be disjoint
input blocks and fix a full binary tree whose leaves are these blocks. At each
internal node $v$, let $L_v,R_v$ be its children's leaf sets. For one common
transcript $Z$, cancellation of internal-node entropy terms gives

$$
\sum_{v\text{ internal}} I(X_{L_v};X_{R_v}\mid Z)
=\sum_{i=1}^k H(X_i\mid Z)-H(X_1,\ldots,X_k\mid Z).
$$

The right side is conditional total correlation. If the input blocks were
initially independent, it equals

$$
I(X_1,\ldots,X_k;Z)-\sum_i I(X_i;Z)\le H(Z).
$$

It is also at most the total input entropy. This is a valid amortization for
one fixed hierarchy and one transcript. It is not a sum over arbitrary
root-level bipartitions, different transcripts at different nodes, or nodewise
conditioning on outside variables. A circuit compiler must justify precisely
the version it uses. Even the valid budget alone charges at most $n$ input bits;
it does not force superlinear computation.

**Conditional extraction still needs an independence estimate.** For $r$-bit
variables $A,B$ and any transcript $Z$, write

$$
k_A=-\log_2\mathbb E_z\max_a\Pr[A=a\mid Z=z],\qquad
k_B=-\log_2\mathbb E_z\max_b\Pr[B=b\mid Z=z],\qquad
\eta=I(A;B\mid Z).
$$

For any sign predictor $g(Z)$, comparison with the distribution
$Q=P_ZP_{A\mid Z}P_{B\mid Z}$ gives

$$
\left|\mathbb E[g(Z)(-1)^{\langle A,B\rangle}]\right|
\le 2^{(r-k_A-k_B)/2}+\sqrt{2\ln(2)\eta}.
$$

Indeed, the Walsh matrix $((-1)^{\langle a,b\rangle})_{a,b}$ has operator
norm $2^{r/2}$. For product conditional marginals with maximum probabilities
$p_z,q_z$, the bias is at most $2^{r/2}\sqrt{p_zq_z}$. Averaging and
Cauchy–Schwarz give the first term. The relative entropy of the true
distribution from $Q$, in natural-log units, is $\ln(2)\eta$. Pinsker's
inequality bounds the difference of expectations of a function of absolute
value at most one by $\sqrt{2\ln(2)\eta}$.

Thus exact prediction when $k_A+k_B\ge r+2h$, $h>0$, implies
$\eta\ge(1-2^{-h})^2/(2\ln2)$. But high marginal min-entropies do not make
$\eta$ small: conditioning independent uniform $A,B$ on $A_1+B_1$ keeps
both marginals uniform and gives one bit of conditional correlation. The
estimate is closely related to [Ko's conditional inner-product lemma](https://arxiv.org/html/2509.02730v1)
(Lemma 3.10). Obtaining small correlation, sufficient entropy, and a gate charge
that counts shared computation once is the unfinished structural step.
