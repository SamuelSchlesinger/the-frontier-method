# What the synthesis adds

[Index](index.md) · [Sources](sources.md)

The strongest transferable idea is to **combine locally valid bounds on the
same conditional transition**, while preserving all information needed for
splicing. The OpenAI manuscripts supply useful designs for local potentials,
globally valid descriptions, and two-way boundary summaries. They do not yet
give the universal supply theorem that would improve our unrestricted circuit
coefficient.

This synthesis adds one checked closure lemma, an experiment measuring
restriction savings and complete-transition costs on the same circuits, and
source-specific transfer obligations. It does not import an upstream theorem
into the Lean dependency graph.

## 1. Combine conditional certificates without losing their hypotheses

Family 119's common-output argument keeps information about a hidden selector
in its local state. Its Shannon-information payment is a useful design principle
for our conditional potentials; it is not itself a bound on the Renyi entropy of
an entire frontier transition. The [capacity analysis](capacity/index.md) gives
the exact quantities and the shared-selector obstruction. [oai119][oai119]

There is a simple compatible combination on our side. Fix one encoding tree,
its parent map, and its actual prefix masses `p(v)`. Suppose both `V` and `W`
satisfy, at every internal node `v`,

```
sum_{u child of v} sqrt(p(u)) V(u) <= sqrt(p(v)) V(v),
sum_{u child of v} sqrt(p(u)) W(u) <= sqrt(p(v)) W(v).
```

Then `U(v)=min(V(v),W(v))` satisfies the same inequality. Indeed the child sum
for `U` is at most each of the two original child sums, hence at most
`min(sqrt(p(v))V(v), sqrt(p(v))W(v)) = sqrt(p(v))U(v)`.
Telescoping gives the global certificate; if both leaf potentials are at least
one, it bounds the sum of square roots of the leaf masses.
This prefix tree encodes one complete graph transition. For each graph layer
there is a separate encoding law, and the supply theorem must bound their roots
uniformly. The lemma does not itself prove coherence across graph layers.

This deduction is now formalized as
`Frontier.Communication.rootPotential_min_step` and
`Frontier.Communication.rootPotential_min_le` in
[Communication.lean](../../Frontier/Boundary/Communication.lean).
The proof uses no upstream result. The connection to family 119 is methodological:
before combining profiles, prove the required local inequality.

Three restrictions matter:

- **Common semantics:** the states, masses, and parent map must agree. Two
  different encodings might need a more expensive common refinement. Two
  one-bit summaries can have a four-valued joint summary.
- **Direction:** these are upper certificates, so minimum is safe. Maximum is
  not: child square-root weights `3/5,4/5` and potentials `(1,4),(4,1)` give
  maximum child cost `28/5`, exceeding the maximum parent budget `19/5`.
- **Root cost:** pointwise minimum initially gives only the better of the two
  root bounds. A strict additional improvement needs retightening ancestors
  after local choices, or a stronger structural estimate. The closure lemma
  supplies no universal small root potential.

The [rational checker](data/check_potentials.py) verifies 625 compatible local
pairs, including 200 strict opportunities to retighten the parent. These finite
examples illustrate the lemma; the general statement is the Lean theorem.

## 2. Measure restriction and capacity on the same circuit

The existing [comparison](../lower-bound-vantages/synthesis.md) proposed pairing
paid restrictions with coherent compression. The
[new probe](data/joint_probe.py) executes a bounded version of that diagnostic.
It uses the existing junction-chain compiler and local normalizer, checks
every input against the original circuit, and evaluates all single-input
restrictions on their entire domains.

Each transition label retains the output class together with the union of its
adjacent-frontier signals, so it determines the complete transition. The reported
moment is for this joint distribution under uniform inputs. The three tested
orders are wire-first, greedy signal-boundary, and a DFS-tree postorder with
larger subtrees first. They are not optimal layouts.

| Circuit | Inputs / gates after normalization | Best tested peak support bits | Best tested peak `H_(1/2)` | Best restriction saves | `g-L` |
|---|---:|---:|---:|---:|---:|
| Parity chain | 6 / 5 | 3.000000 | 3.000000 | 1 | -3.562498 |
| XOR of four independent ANDs | 8 / 7 | 4.000000 | 3.876879 | 2 | -2.562498 |
| XOR of six ANDs sharing one selector | 7 / 11 | 4.169925 | 3.873504 | 11 | 6.437502 |
| Three ANDs of adjacent cycle parities, then XOR | 6 / 11 | 6.000000 | 6.000000 | 4 | -0.562498 |

`g-L` is the exact accounting expression for losing one ambient input dimension
and saving `g` gates, evaluated at `L=4.5624976789...`. The displayed gate counts
are those of the implemented normalizer, not minimum circuit sizes. For the
shared selector the best branch sets it to zero and makes the output constant.
No density or hard-target preservation assertion is being made for that branch.

These easy functions are controls, not instances of the hard extractor family.
The cycle-parity example only identifies a case where these tested layouts and
single-input rules are insufficient; it is not a lower bound against other
layouts, affine changes, or semantic recompilations. The experiment verifies 54
restriction equivalences. Its [recorded output](data/joint-probe.json) is reproduced
by the corpus validator.

## 3. Require complete, context-stable descriptions

The [models analysis](models/index.md) turns the scheduling and two-way-automaton
manuscripts into compiler requirements: descriptions must remain valid in every
allowed context, and a merge must retain all return paths needed by later
composition. A small description for one subproblem or one traversal direction
does not establish a small coherent acceptor.

The practical next step is to annotate each proposed quotient or local
restriction with three separately checked facts: the represented continuation
behavior, its compatibility with adjacent transitions, and its actual transition
count or weighted cost. Our existing representative-quotient and additive
syndrome constructions are baselines, not new discoveries of this synthesis.

## 4. Keep graph candidates on the same numerical scale

The [structural analysis](structure/index.md) finds no immediate replacement for
the Gaussian supply bound. The critical cubic Ising spin cut gives the proxy
`3(1-1/sqrt(2))/2 = 0.4393398...`, exceeding
`A=0.2807019373...`, even before the missing passage from one cut to all cuts of
one ordering. Thin-tree cut bounds compare a spanning tree with the original
graph in a direction that does not bound the latter's layout width.

For a sound representation with `log2 D <= a*s-b*n+o(n)` and current demand
`log2 D >= n-o(n)`, the induced gate coefficient is `(1+b)/a`. In particular,
a supply theorem `log2 D <= B(s-n)+o(n)` would give `1+1/B`.

| Target gate coefficient | Required supply coefficient `B` |
|---|---:|
| Any fixed improvement | `B < A = 0.2807019373...` |
| 4.6 | `1/3.6 = 0.277777...` |
| 4.75 | `1/3.75 = 0.266666...` |
| 5 | `1/4` |

For the average-case route, the corresponding target is a compatible family of
polynomial-length sweeps with complete-transition entropy
`max_t H_(1/2)(Z_t) <= B(s-m)+o(n)` for `m=n-o(n)` reachable inputs. That is
the missing supply theorem. If this holds uniformly and `log K=o(n)`, the
existing moment demand gives the same coefficient with an exponential remainder
for each fixed gap. An entropy estimate alone supplies no efficient enumeration
algorithm and therefore no automatic #SAT speedup.

The next proof target is a dichotomy on candidate hard-function circuits:
profitable restrictions with preserved source hypotheses, or compatible local
certificates with a uniformly better root bound. The new closure lemma and
diagnostics make that target more concrete. Universal structural coverage remains
open.

[oai119]: sources.md#oai119
