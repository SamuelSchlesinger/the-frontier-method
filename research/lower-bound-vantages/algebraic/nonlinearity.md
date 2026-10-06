# Nonlinear gates, affine partitions, and agreement

[Algebraic comparison](index.md) · [Corpus](../index.md)

The model is a Boolean DAG over the full binary basis. Affine means affine over
`F_2`; gates have arbitrary fan-out. The existing total-gate coefficient is
`L=4.562497678925021...`. The deductions below concern a different resource: the
number of nonlinear gates when all affine computation is allowed.

Let `k` count non-affine binary truth tables in the given circuit and `u` its remaining
positive-arity gates, so `s=k+u`. Every binary table has a unique form `c + alpha*a + beta*b +
gamma*a*b` over `F_2`. If `gamma=1`, it equals `(a+beta)(b+alpha)+c+alpha*beta`. Thus it uses
one multiplication and affine operations; negations are offsets. After constant and unary
propagation, this gives AND/XOR gates with complemented wires at the same binary-gate count:
absorb each output offset into its consumers, retaining a possible output NOT. It preserves
total cost up to that one output gate while XOR gates stay paid; passing to multiplicative
complexity subsequently makes them free.

Introducing one variable `z_i` for each such product yields the exact triangular system
`z_i=U_i(x,z_<i)*V_i(x,z_<i)`, with affine `U_i,V_i`, and an affine output in `(x,z)`. For each
input there is exactly one full assignment to the `z_i`, by induction. This permits sharing and
arbitrary binary truth tables without expanding them into a formula. Dropping any defining
equation loses exactness.

**Known lemma, with proof.** A circuit with `k` multiplications is affine on a nonempty affine
subspace of dimension at least `n-k`. Process its multiplication gates in order. Their operands
are affine on the current subspace. If the first operand is nonconstant, impose its zero
hyperplane, losing one dimension; if it is constant, no restriction is needed. In either case
the gate becomes affine. One further hyperplane makes the final affine output constant, so a
monochromatic flat has dimension at least `n-k-1` whenever this bound is nonnegative. This
weak-normality argument is established in the multiplicative-complexity and affine-disperser
literature. [boyar16][boyar16] [demenkov11][demenkov11]

**Deduction for the current target.** Put `q=ceil(log_2 K)`. Sumset bias strictly below one in
sign-bias convention forbids monochromatic affine subspaces of dimension at least `q`: take
independent uniform sources on `a+V` and `V`. If `k<=n-q-1`, the lemma produces such a subspace.
Consequently `k>=n-q`, including the inclusive threshold and the extra output hyperplane. For
`log K=o(n)` this requires `n-o(n)` nonlinear gates. This is a proved corollary newly recorded
here, not a claim of a new normality theorem or priority. It cannot be added to `s>=Ln-o(n)`:
both bounds charge the same circuit.

**Average-case corollary (paper deduction).** The normality construction can branch
on both values of each affine operand, instead of selecting one. It partitions the
whole input cube into at most `2^(k+1)` disjoint monochromatic affine flats for the
circuit, each of dimension at least `n-k-1` when that bound is nonnegative. At each
nonlinear gate the already processed operands are affine on each current flat;
fixing either value of one nonconstant operand drops dimension by one and makes
the gate affine. Empty branches are omitted. Split the final affine output once
more. This proves the partition claim by induction and retains all circuit inputs.

Consequently, if a target has sign bias at most `2b` on every affine flat of
dimension at least `q`, **every** circuit with `k<=n-q-1` nonlinear gates has
uniform-input agreement at most `1/2+b`, regardless of its number of affine gates.
On each leaf the circuit is constant and the target satisfies that agreement
bound; average over the disjoint leaves with their actual uniform-input masses.
Sumset-extractor bias supplies the flat hypothesis as above. This strengthens the
resource-specific deduction to approximate computation; it does not raise the
total-gate coefficient or assert a new result of historical priority.

[boyar16]: ../sources.md#boyar16
[demenkov11]: ../sources.md#demenkov11
