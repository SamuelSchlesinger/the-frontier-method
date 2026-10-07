# Information and complete-transition capacity

**Verdict.** Family 119 supplies a conditional-payment proof design, but its Shannon
and Hellinger theorems do not bound Frontier's complete-transition moment.
A direct linear thinning rule for that moment is false. The usable transfer is
a certificate on actual joint prefix laws, followed by a new circuit-size bound
on its initial value. No improved unrestricted coefficient follows here.

[Back to the synthesis](../index.md). Upstream: `adc7f1241b42e322a6451854ab7e4b4c146bf78a`;
local baseline: `f8e6d32df24a7a42930edd921b7e896b6b8cc4aa`. We distinguish upstream
claims, inspected formal statements, our deductions, and finite checks.

## The local demand is already a fractional moment

For uniform `X` in `{0,1}^n`, coherent nested sweeps of the predictor's output
classes, and a target of rectangle bias `β` at threshold `K>1`, put

```text
Z_t = (g(X), old_message_t, new_message_t, newly_read_input_values_t),
p_t(z) = Pr[Z_t=z],                    Λ = (K-1)^2 / 2^n,
R_θ(p) = Σ_z p(z)^θ,                  H_θ(p) = log_2 R_θ(p)/(1-θ).
```

Assume a common polynomial layer count `T`; the individual output-class masses
in `p_t` are unconditional. `Capacity.lean` supplies, for fixed `0<θ<1`,

```text
agreement(f,g) ≤ (1+β)/2 + (1/2) Λ^(1-θ) Σ_t R_θ(p_t).
```

This follows from its capped charge `Σ min(Λ,p)` and
`min(Λ,p) ≤ Λ^(1-θ)p^θ`. The square-root case is `θ=1/2`.
`Sweep.transition` contains both adjacent messages and the new input values;
a marginal boundary-bit estimate omits part of the demand. The local theorem
assumes no independence. Samuel Schlesinger's formalization and research note
credit Sam McGuire for the underlying weighted peeling argument. [frontier][frontier]

## What family 119 actually controls

The binary-information paper uses nats: `L=ln 2`, `h(r)=h_bin((1+r)/2)`, `ψ(r)=L-h(r)`, and
`I(u)=h(Eu)-E h(u)` for a soft binary channel `u` on a uniform cube.
Its claimed sharp statement is
`I(T_ρu) ≤ ψ(|ρ| ψ^(-1)(I(u)))`, where `T_ρ` is independent symmetric
coordinate noise. Soft coordinate channels attain the bound. This is the
information between one binary summary and the noisy cube, rather than the
entropy of an arbitrary vector of circuit signals. [oai119][oai119]

The mechanism to inspect is `build/sections/thinning.tex`. For an interior core
with conditional output means `c+d,c-d`, `c≥0`, `d>0`, `c+d<1`, an independent
flag `B` selects the core with probability `λ∈(0,1]`; otherwise the output sign
`U` is constantly `+1`. With a fair input sign `X`, define

```text
x = 1-λ(1-c),      e = λ[h(c+d)+h(c-d)]/2,
I = h(x)-e,        ν = [h(x+λd)+h(x-λd)]/2-e,
J = I-ν,           J_c = h(c)-[h(c+d)+h(c-d)]/2,
F(s) = ψ^(-1)(s) atanh(ψ^(-1)(s)),             0≤s<L.
```

The claimed payment is `F(ν+J)-F(ν) ≤ λF(J_c)`;
`I=I(U;X,B)`, `ν=I(U;B|X)`, and `J=I(U;X)`.
The flag-information term is retained. The proof makes the normalized
increment monotone in `λ`, using `F'≥2`,
`F''(s)≤(4L²/3)/(L-s)²`, and the positive margin `2-4L²>0`.
This is a specific Shannon rate comparison, not an assertion that arbitrary
information costs shrink linearly when a common output is added. [oai119][oai119]

`build/sections/upgrade.tex` combines the rate with a mean-dependent reserve:
`S(s)=F(s)-2s` for `s≥0` and zero for `s<0`, and
`B_m(I)=2I+(1-m²)S(L-(h(m)-I)/(1-m²))`.
The production lower profile is `max(B_m(I),F(I))`. Above `I=L/2` the reserve
dominates; below it a reflected-core comparison reduces to one-corner payment.
Each original child entropy stays in its child profile; replacing those with
the optimizer's child entropies is invalid.
Courtade and Kumar formulated the information conjecture; Chen, Gohari, and Nair
supplied the differential local-to-global framework and maximum-closure lemma. [oai119][oai119] [ck14][ck14] [cgn25][cgn25]

The separate Hellinger manuscript claims, for Boolean `f`,

```text
sqrt(1-m²) - E sqrt(1-(T_ρf)²) ≤ 1-sqrt(1-ρ²),       m=Ef.
```

For nonconstant `f` the left side is
`sqrt(1-m²)[1-Aff(P_+,P_-)]`, with `P_±=Law(Y|f(X)=±1)`.
It controls the overlap between two conditional observation laws. It does not
control `Σ_z sqrt(Pr[Z_t=z])`; even a constant binary summary can coexist with
an arbitrarily long uniform observed vector. Anantharam, Bogdanov, Chakrabarti,
Jayram, and Nair introduced this formulation and its implication to the Boolean
Shannon conjecture. The companion source asserts no implication to the full
soft-channel theorem. [oai119h][oai119h] [abcjn17][abcjn17]

## Inspected formal scope

Upstream uses Lean `v4.34.1` and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`; Frontier uses Lean `v4.35.0-rc3`.
The comparator `.lean` files are target statements containing deliberate
`sorry`s. Their `.json` files point to solutions in `OAI`, permit only
`propext`, `Quot.sound`, and `Classical.choice`, and set `enable_nanoda=false`.
We read these implementations and scope documents without compiling upstream
or running Comparator. Configuration is not a verification result. [oai-lean][oai-lean]

| Family | Inspected OAI implementation and actual endpoint |
| --- | --- |
| 119 | `InformationTheory/SoftChannel/Payment.lean`: `common_output_payment`; `Joining.lean` and `Production.lean`: local comparisons and production; `Main.lean`: `OAI.SoftChannel204.fullMain`. `BooleanNoise/Main.lean` supplies the Courtade–Kumar endpoint. |
| 140 | `Probability/GaussianRegression/Main.lean`: `OAI.NoiselessRegression.main`, subquadratic and fixed-quadratic memory bounds. `Probability/PosteriorReplicas/Main.lean`: `source_main`, exact-label comparisons and a kernel-learner bound. |
| 229 | `Probability/ThreeState/Supercritical.lean`: `regular_supercritical` and `poisson_supercritical`, exposed by `Main.lean`. The selected comparison is reconstruction above Kesten–Stigum. |

`lean/docs/119.md` names the binary-information paper, not the Hellinger manuscript
or its arithmetic certificates. `lean/docs/229.md` selects supercritical
three-state reconstruction only, not the catalogue's full three/four-state
threshold and capacity headline. Partial converse results elsewhere in that
source do not close this scope gap. [oai-lean][oai-lean]

## Proved deduction: the correct common-output charge

For a distribution `q` on a finite alphabet, a symbol `z₀`, and `0<θ<1`, let
`p=(1-λ)δ_z₀+λq`. Subadditivity of `a↦a^θ` gives

```text
R_θ(p) ≤ (1-λ)^θ + λ^θ R_θ(q).                       (1)
```

This is the flagged variable `(B,Z)`'s exact moment before merging its copies of
`z₀`; disjoint supports give equality. A linear analogue
`R_θ(p)-1 ≤ λ(R_θ(q)-1)` fails for `q=δ_z₁`, `z₁≠z₀`: its right side is zero and
left side positive. This falsifies a scaling transfer, not the Shannon theorem.
Equation (1) is a paper deduction checked against enumerated distributions below.

At an encoding prefix `v` of positive mass, the local certificate is

```text
Σ_{u child of v} Pr[u|v]^θ V_θ(u) ≤ V_θ(v),   V_θ(leaf)≥1.    (2)
```

Multiplying by `Pr[v]^θ` and summing each level telescopes to
`R_θ(Z_t)≤V_θ(root)`. The `θ=1/2` version is the baseline
`Communication.rootPotential_le`; general `θ` here is an elementary paper
deduction. Two compatible upper certificates on identical masses and parent
maps may use their pointwise minimum: each child contribution decreases, and
the sum is at most each original parent bound. The new local Lean lemmas
[`rootPotential_min_step` and `rootPotential_min_le`](../../../Frontier/Boundary/Communication.lean)
were checked during this investigation. Their root remains `min(V(root),W(root))`;
extra saving requires new root estimates or retightening the ancestors.
This upper-bound minimum is the appropriate counterpart of the source's
production-lower-bound maximum, with no claim of novelty. [frontier][frontier] [cgn25][cgn25]

## Shared selectors and output conditioning

Revisit the local communication note's shared-selector obstruction: independent
fair bits `B,X₁,…,X_k` feed `Y_i=B AND X_i`. Then `p(0^k)=1/2+2^(-k-1)` and every
other word has mass `2^(-k-1)`. For every fixed `θ∈(0,1)`, [frontier][frontier]

```text
R_θ(Y)=(1/2+2^(-k-1))^θ+(2^k-1)2^(-(k+1)θ),
H_θ(Y)=k-θ/(1-θ)+o(1),       H_1(Y)=k/2+1-o(1).
```

Choosing a fixed `θ` nearer one still gives no linear-in-`k` moment saving.
At `k=12`, Shannon entropy is `6.99835902`, root entropy `11.04404736`, and the
sum of marginal root entropies `10.79962352`. Marginal Rényi subadditivity fails
here. Once a one has appeared, the remaining outputs are fair.

For the readout `G=XOR_i Y_i`, conditioning on `G=1` forces `B=1` and makes `Y`
uniform on `2^(k-1)` odd words, so every `H_θ` equals `k-1`. Even two fair inputs
cease to be independent conditional on XOR zero: the joint support is `{00,11}`.
Retain actual conditional laws or unconditional class masses; output bias does
not preserve product input laws. This obstructs a distribution shortcut, not
every layout: the readout simplifies to `B AND XOR_i X_i`.

There is a safe, proved output-bit rule for any joint `(Z,G)`:
`R_θ(Z,G)≤2^(1-θ)R_θ(Z)`, since the conditional binary moment is at most
`2^(1-θ)`. Hence appending one output bit costs at most one entropy bit when a
common transition encoding is available. Class-specific encodings must instead
retain their disjoint masses. No independence is used in this deduction.

## Exact missing lemma and bounded comparisons

**Proposed supply lemma, unproved.** Find fixed `0<θ<1` and `B<A` such that every
fan-in-two circuit with `s` positive-arity gates and `m=n-o(n)` reachable inputs
admits coherent nested output sweeps, polynomially many layers, and encodings
whose leaves recover the complete transitions and satisfy (2) with

```text
log_2 V_{θ,t}(root) ≤ (1-θ)[B(s-m)+o(n)]   uniformly in t,
A = (3/π) acos((1+2sqrt(2))/4) = 0.280701937272… .
```

Together with `log K=o(n)`, this would give average-case hardness below
`(1+1/B-ε)n` with exponential remainder for fixed `ε>0`; the local unused-input
argument handles the other regime. `B=1/4` would give `5n`, versus today's
`4.562497678925…n`. Neither family 119 nor minimum closure proves this root
budget. A valid transfer must justify the actual conditional laws and charge
the complete transition using total circuit size. [frontier][frontier]

Family 140's replica inequality is `t I(S;W|B,φ_B(S))≤H(W)+K-K'`: `K` is total correlation
of the replicas and `K'` the correlation surviving projection. It requires
matching signal–message pair laws and independent `B`, including after conditioning.
The regression endpoints keep fresh Gaussian rows, a spherical prior, and finite
persistent states. Translating these experiments to circuit traces and from
Shannon information to (2) is unproved. [oai140r][oai140r] [oai140][oai140]

Family 229 models independent broadcast branches conditional on a root spin;
its selected three-state results give positive limiting recovery advantage when
`dλ²>1`. Circuits share ancestors and reconverge, as the selector example does.
A tree recursion needs a proved conditioning separator and a payment for that
separator to control a circuit transition. Its recoverability lower bound also
differs in direction from the required upper encoding budget. [oai229][oai229]

## Reproduction and remaining limits

Run [`data/check_transfer.py`](data/check_transfer.py) from the repository root;
[`data/expected.txt`](data/expected.txt) records 12 rejected linear moment rules,
16 selector/moment/output cases, and the two-bit conditioning counterexample.
Algebra proves the deductions; floating-point checks guard transcription.
Upstream Lean and Hellinger arithmetic certificates were not replayed.

[frontier]: ../sources.md#frontier
[oai119]: ../sources.md#oai119
[ck14]: ../sources.md#ck14
[cgn25]: ../sources.md#cgn25
[oai119h]: ../sources.md#oai119h
[abcjn17]: ../sources.md#abcjn17
[oai-lean]: ../sources.md#oai-lean
[oai140r]: ../sources.md#oai140r
[oai140]: ../sources.md#oai140
[oai229]: ../sources.md#oai229
