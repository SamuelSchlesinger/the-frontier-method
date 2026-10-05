import Frontier

/-!
Audit the principal theorem dependencies. Each guard fails if Lean reports an axiom list
different from the standard three below, including a dependency on `sorryAx`.
Run after `lake build --wfail` with `lake env lean scripts/Audit.lean`.
-/

/-- info: 'Frontier.layoutBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.layoutBound_gaussian

/-- info: 'Frontier.lowerBound_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_gaussian

/-- info: 'Frontier.lowerBound_sumsetDisperser' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_sumsetDisperser

/-- info: 'Frontier.lowerBound_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_linear

/-- info: 'Frontier.arith_cauchy_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.arith_cauchy_gaussian

/-- info: 'Frontier.cauchyZMod_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.cauchyZMod_gaussian

/-- info: 'Frontier.lowerBound_ledger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_ledger

/-- info: 'Frontier.lowerBound_aggregate_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_aggregate_gaussian
