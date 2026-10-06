# Algebraic and analytic methods

[Return to the comparison](../index.md). Literature metadata checked 2026-10-06. The target
remains single-output, unrestricted fan-in-two Boolean DAGs over the full binary basis, with
positive-arity gates counted and sharing allowed. Write `A=0.280701937...` and
`L=1+1/A=4.562497678...` for the existing constants. None of the arithmetic results below
improves that Boolean coefficient by itself.

The promising algebraic interface is exact affine compression with nonlinear equations retained.
The existing [affine preparation](../../communication/restrictions.md), [syndrome
compiler](../../communication/additive.md), and [joint code](../../communication/joint.md)
already implement important parts of this interface. Their results are inputs to this
comparison, not new discoveries.

| Mechanism | Resource it actually controls | Frontier component it might change | Transfer obligation |
|---|---|---|---|
| Polynomial approximation and Fourier concentration | Degree, error, spectrum, usually at bounded depth | A terminal or an additional hard-target property | Relate these parameters to the same paid DAG |
| Derivative and coefficient spaces | Restricted arithmetic size or ordered ABP width | A dimension-based supply bound | Preserve field, variable order, and positive accepting semantics |
| Rigidity and volume | Linear size/depth or bounded-coefficient operations | Cost of affine interfaces | Retain prefix cost and simultaneous suffix layout |
| Tensor rank and algebraic geometry | Bilinear rank, border complexity, orbit-closure containment | Cut invariants and exact local compression | Convert decompositions to actual transitions without cancellation |
| Monotone support methods | Positive semiring circuits or monotone Boolean size | Additive demand and paid support compilation | Preserve support under every gate and charge reused computations |

## Finite-field approximation, real approximation, and Fourier analysis

A probabilistic polynomial over `F_p` is a distribution of polynomials with `Pr[P(x)=f(x)] >=
1-epsilon` for every Boolean input. Degree and pointwise failure probability are its parameters.
This is different from a single real polynomial satisfying `|P(x)-f(x)|<=epsilon` everywhere,
and from approximation only on most inputs under a specified distribution.

Razborov and Smolensky exploit low-degree approximation for bounded-depth circuits with modular
gates. For distinct fixed primes `p,q`, their results give superpolynomial size lower bounds for
`MOD_q` against constant-depth `AC^0[p]`, with unbounded AND/OR/MOD-p gates and negations.
Characteristic matters: an `F_2` parity gate is linear, whereas real parity has degree `n`.
This does not give the required size-to-degree bound for unrestricted Boolean DAGs.
[razborov87][razborov87] [smolensky87][smolensky87]

For real approximation, Paturi determines constant-error approximate degree of symmetric Boolean
functions. Threshold degree asks only for a polynomial of the correct strict sign; coefficient
weight and margin are additional resources, not interchangeable definitions. Sherstov's
pattern-matrix method transfers approximate degree and related dual witnesses to specific
communication matrices. That transfer has a gadget and a communication model; it is not an
arbitrary-cut frontier compiler. [paturi92][paturi92] [sherstov11][sherstov11]

Linial--Mansour--Nisan give low-degree Fourier concentration for constant-depth `AC^0`, with
uniform-distribution squared-error meaning. This suggests searching for terminals with a
controlled spectrum, but neither low influence nor a sparse spectrum supplies a gate deletion or
a coherent low-cost sweep on an arbitrary shared DAG. [linial93][linial93]

**Exact preservation test.** Over `F_2`, an invertible affine input map preserves algebraic
degree and multiplicative complexity. Over the real Fourier basis it permutes characters,
preserving their coefficient magnitudes but not their Hamming degrees. The invertible map
`T(x)=(x_1 XOR ... XOR x_n,x_2,...,x_n)` turns the projection `y_1` into parity. Its real degree
and constant-error approximate degree are `n`: a polynomial of degree below `n` is orthogonal to
the parity character, contradicting pointwise error below one for the sign encoding. Real degree
therefore cannot be silently carried through the repository's affine preparation.

The same example falsifies free substitution in the paid model: the projection needs no gate;
parity needs at least `n-1` binary gates. Indeed, a connected ancestor DAG with `n` essential
inputs and `s` binary gates has at most `2s` edges but at least `n+s-1` edges. Sumset hardness
survives this pullback; gate cost does not. A useful approximation bridge must bound both the
transformed model's error and its gate or state cost with an explicit leading constant.

## Partial derivatives, shifted partials, and evaluation dimension

Nisan--Wigderson measure the span of formal partial derivatives and obtain lower bounds for
restricted arithmetic circuits. Shifted partials span polynomials `m * partial_alpha(f)`, with
derivative order and monomial degree prescribed; their power comes from a restricted circuit's
upper bound on this span. Homogeneity, depth, field characteristic, and the exact
shifted/projected variant belong in the theorem statement. [nisanwigderson96][nisanwigderson96]

For example, Kayal--Limaye--Saha--Srinivasan prove exponential lower bounds for homogeneous
depth-four formulas in characteristic zero. Later low-depth work extends the scope beyond that
single depth; Amireddy and coauthors directly bound shifted partials of homogeneous formulas in
their low-degree regime. Neither result is a lower bound for unrestricted-depth Boolean DAGs
merely because their gate operations admit arithmetic encodings. [kayal17][kayal17]
[amireddy23][amireddy23]

Evaluation dimension at a cut spans residual polynomials after evaluating a prefix of variables.
For multilinear polynomials, Boolean evaluations already recover the coefficient span; for
higher individual degree one needs a sufficient evaluation grid or extension field. Ordered
read-once oblivious ABP width is characterized by the associated coefficient ranks. This is a
natural comparison to a frontier state, but its states are linear combinations with field
weights. [nisan91][nisan91] [forbesshpilka13][forbesshpilka13]

Three failures rule out an automatic transfer. First, Boolean identities such as `x^2=x` hold
only after quotienting by the Boolean ideal; a formal polynomial computed by an arithmetized DAG
need not be the target's multilinear extension. Second, in characteristic `p`, ordinary
derivatives annihilate `x^p`; Hasse derivatives address that issue but do not solve the model
conversion. Third, expanding a DAG into a formula charges each reused subcomputation again. Any
derivative bridge must specify an exact polynomial lift, retain these costs, and prove its
demand for that lift rather than for an unrelated polynomial.

## Noncommutative and multilinear ranks

For a homogeneous noncommutative polynomial of degree `d`, Nisan's matrix `M_k` has words of
lengths `k` and `d-k` as indices and their concatenation coefficient as entry. Its ranks
lower-bound ABP layers, and their sum characterizes the homogeneous ABP size under the standard
vertex convention; formula lower bounds follow through the formula-to-ABP conversion. This
preserves ordered products, not a commutative Boolean computation with arbitrary reuse.
[nisan91][nisan91]

Raz's superpolynomial permanent/determinant lower bounds concern multilinear arithmetic
formulas, whose intermediate polynomials remain multilinear. Syntactic multilinearity
additionally requires disjoint variable sets at product gates. Neither property follows from the
final Boolean function having a unique multilinear representation. The random-partition argument
controls formula structure; it does not assert that every partition has low rank. [raz09][raz09]

**Two small falsifications.** The polynomial `prod_i(x_i+y_i)` has a formula with `2m-1`
arithmetic gates but coefficient rank `2^m` across `X|Y`: its matrix is the complementary-subset
permutation matrix. A large rank at a chosen partition therefore is compatible with a small
formula. Also, the Boolean index function `f(x,j)=x_j`, with `r` data bits and a binary-encoded
index, has `2^r` distinct prefix residuals but evaluation span dimension `r` when `r` is a power
of two. Linear dimension does not equal the number of deterministic states. This second example
does not lower-bound nondeterministic state count; an index guess can exploit a different
representation.

A valid frontier bridge would construct, at every layer, a **nonnegative** factorization whose
supports remain valid additive transitions, and would bound the sum of transition counts, not
just the maximum field rank. Signed rank factorizations can cancel rejecting assignments. Even
`a XOR b=a+b-2ab` shows the issue: unioning the three term supports falsely accepts `(1,1)`.

## Rigidity, bounded coefficients, and the affine-prefix bill

Matrix rigidity `R_M(r)` is the minimum number of entries changed to bring the rank of `M` below
or equal to `r`, over a specified field. Valiant relates strong rigidity to size/depth lower
bounds for circuits computing many linear outputs. This is a way to study costly linear
transformations, with depth and output count included, not a lower bound for a single arbitrary
Boolean output. [valiant77][valiant77]

Morgenstern's volume argument bounds linear computations with bounded complex coefficients,
giving an `Omega(n log n)` Fourier-transform lower bound in that model. Removing the coefficient
bound removes its uniform per-operation volume charge: one allowed enormous scalar can increase
volume enormously. Over `F_2` there is no comparable absolute-value volume. Conversely, a lower
bound for XOR-only computation does not automatically apply to nonlinear circuits that happen to
produce a linear map. [morgenstern73][morgenstern73]

Alman--Williams' nonrigidity result for Walsh--Hadamard matrices is a useful warning: familiar
Fourier structure is not evidence for the rigidity parameters needed in a particular reduction.
One must calculate the actual matrix and rank/change regime. [alman17][alman17]

For the frontier method, keep the real prefix bill `ell` and the joint rank profile `rho(P,Q)`
already defined in the [joint note](../../communication/joint.md). The concrete problem is to
exploit relations of a low-cost affine implementation while laying out its arbitrary nonlinear
suffix. An expensive basis conversion, or a rank-optimal order incompatible with that suffix,
spends the intended gain.

## Tensor rank, border rank, and algebraic geometry

For a bilinear map, tensor rank counts products of one linear form from each input block,
allowing free linear preprocessing and output combinations. This already differs from total
binary Boolean gate count. Flattening rank is a lower bound on tensor rank, but can miss
higher-order structure. Raz gives a genuine transfer from sufficiently strong explicit
high-order tensor-rank bounds to arithmetic **formula** lower bounds, with explicit order
parameters; it is not the needed constant-preserving Boolean DAG transfer. [raz13][raz13]

Border rank permits limits of rank-`r` tensors over the chosen algebraic setting. Bini and
coauthors show why approximate bilinear algorithms matter for matrix multiplication. Such
degenerations are not accepting-path certificates: their coefficients may diverge, signs may
cancel, and extracting an exact answer needs an additional procedure. Exact tensor rank, border
rank, and nonnegative rank must therefore remain separate resources. [bini79][bini79]

Mulmuley--Sohoni's geometric complexity theory organizes algebraic separation through orbit
closures and representation theory. The permanent-versus- determinant setting is over complex
polynomials with padding and specified linear substitutions. Bürgisser--Ikenmeyer--Panova rule
out the proposed class of occurrence obstructions in that setting, not all multiplicity
obstructions or all GCT. No Boolean leading constant follows from merely expressing frontier
constraints as a variety. [mulmuley01][mulmuley01] [burgisser19][burgisser19]

The actionable tensor question is local: can a Boolean constraint tensor be replaced by a
smaller network with nonnegative entries, exactly the same support on all exposed wires, and a
proved total gate/transition saving? A field basis change alone lacks these conditions. Track
exposed-wire sharing and all scalar constants; demand for a positive additive generator survives
only after support soundness has been proved.

## Monotone Boolean approximation versus arithmetic and tropical support

Razborov's monotone approximation method controls combinatorial approximators under positive and
negative test distributions for monotone AND/OR circuits. It is neither finite-field
probabilistic degree nor real uniform approximation. Its use of monotonicity obstructs direct
application to XOR or arbitrary binary truth tables. [razborov85][razborov85]

Jerrum--Snir's monotone arithmetic and semiring bounds exploit the impossibility of canceling
unwanted monomials. Supports multiply by Minkowski addition and add by union, giving product
decompositions useful for support lower bounds. Tropical min-plus/max-plus circuits use a
different equality of computed functions; dominated monomials may be invisible. Jukna's
conversion to arithmetic circuits has a multilinearity hypothesis, explicitly corrected in the
paper's revision. Do not apply it to arbitrary nonmultilinear tropical polynomials or to
algorithms with unrestricted branching. [jerrum82][jerrum82] [jukna15][jukna15]

The repository's additive demand already draws on this support tradition. Its advantage is
tolerance of colliding accepting paths. Its restriction is that every path generates a valid
point. Arithmetic cancellation violates that restriction. A promising bridge would compile gates
into support-preserving relations, charging sharing only once; replacing each arithmetic sum by
union fails on the two-input XOR example above. Existing sumset and syndrome results must not be
relabeled as a new application of monotone arithmetic.

## Multiplicative complexity as an additional constraint

The [nonlinear-gate and affine-partition analysis](nonlinearity.md) gives the
triangular XOR/AND normal form, the credited affine-normality lemma, and its exact
and average-case consequences for the extractor target. It proves that roughly
`n` nonlinear gates are necessary even with free affine computation; it does not
add this cost to the current total-gate lower bound.

## Concrete bridges, falsification tests, and stopping rules

The best immediate target is a **mixed supply theorem** for a paid XOR-AND description: retain
`u`, `k`, original dimension, all quadratic equations, and the chosen cut information. Prove an
additive generator with `log_2 D <= B(s-n)+o(n)` for some fixed `B<A` on a specified residual
class. Together with additive demand this gives coefficient `1+1/B`; `B=1/4` gives five. The
nonlinear demand `k>=n-q` can constrain that class. It does not itself justify subtracting a
bonus per nonlinear gate; AND trees have many such gates and are an immediate test of any
universal negative-discount formula.

For an affine restriction of codimension `h`, let `g` gates disappear and let `t` gates be added
to implement substitutions. Its exact deficit change is `(5(n-h)-(s-g+t))-(5n-s)=g-t-5h`. A paid
affine restriction therefore preserves the five-target deficit only if `g-t>=5h`. Count dense
XOR substitutions and bypasses, and stop this route if the only witness needs an uncharged
substitution.

For a rank-based terminal, first prove an exact nonnegative realization with compatible
transitions and count its total size. Test the index function, `prod_i(x_i+y_i)`, XOR
cancellation, and shared nonlinear outputs before searching for a universal inequality. If the
result yields only signed contraction cost, record it as a different representation; the current
additive demand does not apply. Even a successful restricted terminal needs the global coverage
theorem.

## Validation and limitations

[The finite checker](data/check_bridges.py) verifies all 16 binary tables, triangular
normalization, monochromatic-flat certificates, and full affine partitions for 240
generated circuits on 5,952 inputs,
and the degree, residual-state, partition-rank, and cancellation counterexamples. [Expected
output](data/expected.txt) is reproducible with `python3
research/lower-bound-vantages/algebraic/data/check_bridges.py`. These checks test
implementations and finite witnesses; the proofs above carry the general claims. No compiler
with `B<A`, global coverage theorem, or new unrestricted Boolean lower-bound coefficient is
proved here.

[alman17]: ../sources.md#alman17
[amireddy23]: ../sources.md#amireddy23
[bini79]: ../sources.md#bini79
[burgisser19]: ../sources.md#burgisser19
[forbesshpilka13]: ../sources.md#forbesshpilka13
[jerrum82]: ../sources.md#jerrum82
[jukna15]: ../sources.md#jukna15
[kayal17]: ../sources.md#kayal17
[linial93]: ../sources.md#linial93
[morgenstern73]: ../sources.md#morgenstern73
[mulmuley01]: ../sources.md#mulmuley01
[nisan91]: ../sources.md#nisan91
[nisanwigderson96]: ../sources.md#nisanwigderson96
[paturi92]: ../sources.md#paturi92
[raz09]: ../sources.md#raz09
[raz13]: ../sources.md#raz13
[razborov85]: ../sources.md#razborov85
[razborov87]: ../sources.md#razborov87
[sherstov11]: ../sources.md#sherstov11
[smolensky87]: ../sources.md#smolensky87
[valiant77]: ../sources.md#valiant77
