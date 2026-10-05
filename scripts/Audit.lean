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

/-- info: 'Frontier.lowerBound_nondeterministic_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_nondeterministic_gaussian

/-- info: 'Frontier.Compiler.ncard_accepted_le_signals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.ncard_accepted_le_signals

/-- info: 'Frontier.Compiler.cycleRankOn_add_ncard_readIn_le_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.cycleRankOn_add_ncard_readIn_le_local

/-- info: 'Frontier.Ledger.total_run_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Ledger.total_run_eq_iff

/-- info: 'Frontier.Sweep.abs_sumOn_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.abs_sumOn_le_of_budget

/-- info: 'Frontier.averageCase_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.averageCase_abs

/-- info: 'Frontier.averageCase_sumset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.averageCase_sumset

/-- info: 'Frontier.layoutBound_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.layoutBound_one

/-- info: 'Frontier.lowerBound_all_fanIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_all_fanIn

/-- info: 'Frontier.Compiler.signalCut_submodular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.signalCut_submodular

/-- info: 'Frontier.LinearBoundary.ncard_syndromes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.ncard_syndromes

/-- info: 'Frontier.LinearBoundary.ncard_syndromes_le_states' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.ncard_syndromes_le_states

/-- info: 'Frontier.Sweep.abs_sumOn_le_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.abs_sumOn_le_codes

/-- info: 'Frontier.Sweep.transitionCount_le_linear_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.transitionCount_le_linear_codes

/-- info: 'Frontier.agreement_le_pruned_sweeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.agreement_le_pruned_sweeps

/-- info: 'Frontier.Network.abs_sumOn_accepted_le_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Network.abs_sumOn_accepted_le_tree

/-- info: 'Frontier.LocalLayout.cutSize_improve_cubic_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LocalLayout.cutSize_improve_cubic_le
