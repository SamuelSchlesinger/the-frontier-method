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

/-- info: 'Frontier.SumsetDisperser.sumsetFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.SumsetDisperser.sumsetFree

/-- info: 'Frontier.AdditiveSweep.ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.AdditiveSweep.ncard_le

/-- info: 'Frontier.AdditiveSweep.transitionCount_le_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.AdditiveSweep.transitionCount_le_codes

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

/-- info: 'Frontier.FlatSumsetBias.affine_pullback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.FlatSumsetBias.affine_pullback

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

/-- info: 'Frontier.LinearBoundary.finrank_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.finrank_joint

/-- info: 'Frontier.Sweep.abs_sumOn_le_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.abs_sumOn_le_codes

/-- info: 'Frontier.Sweep.transitionCount_le_linear_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.transitionCount_le_linear_codes

/-- info: 'Frontier.agreement_le_pruned_sweeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.agreement_le_pruned_sweeps

/-- info: 'Frontier.Sweep.abs_sumOn_le_capped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.abs_sumOn_le_capped

/-- info: 'Frontier.Sweep.cappedCapacity_le_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.cappedCapacity_le_root

/-- info: 'Frontier.agreement_le_capped_sweeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.agreement_le_capped_sweeps

/-- info: 'Frontier.agreement_le_root_sweeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.agreement_le_root_sweeps

/-- info: 'Frontier.Sweep.cappedCapacity_le_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.cappedCapacity_le_moment

/-- info: 'Frontier.agreement_le_moment_sweeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.agreement_le_moment_sweeps

/-- info: 'Frontier.Communication.rootPotential_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Communication.rootPotential_le

/-- info: 'Frontier.Network.abs_sumOn_accepted_le_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Network.abs_sumOn_accepted_le_tree

/-- info: 'Frontier.LocalLayout.cutSize_improve_cubic_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LocalLayout.cutSize_improve_cubic_le

/-- info: 'Frontier.Decomposable.ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Decomposable.ncard_le

/-- info: 'Frontier.Gaussian.sum_unitKernel_mul_ge_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.sum_unitKernel_mul_ge_degree

/-- info: 'Frontier.Gaussian.vertexLayout_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.vertexLayout_bound

/-- info: 'Frontier.layoutBound_two_fifths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.layoutBound_two_fifths

/-- info: 'Frontier.lowerBound_fanInThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_fanInThree

/-- info: 'Frontier.Compiler.pow_le_cutSignals_mul_fibers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.pow_le_cutSignals_mul_fibers

/-- info: 'Frontier.mds_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.mds_gaussian

/-- info: 'Frontier.TotallyRegular.isMDS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.TotallyRegular.isMDS

/-- info: 'Frontier.IsMDS.permute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.IsMDS.permute

/-- info: 'Frontier.linear_finite_fanInThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.linear_finite_fanInThree

/-- info: 'Frontier.linear_polynomial_fanInThree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.linear_polynomial_fanInThree

/-- info: 'Frontier.layoutBound_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.layoutBound_degree

/-- info: 'Frontier.Gaussian.degreeCoefficient_lt_three_quarters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.degreeCoefficient_lt_three_quarters

/-- info: 'Frontier.Multigraph.Compression.Terminal.multi_edge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.Compression.Terminal.multi_edge_bound

/-- info: 'Frontier.lowerBound_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_degree

/-- info: 'Frontier.linear_finite_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.linear_finite_degree

/-- info: 'Frontier.linear_polynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.linear_polynomial_degree

/-- info: 'Frontier.mds_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.mds_degree

/-- info: 'Frontier.averageCase_sumset_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.averageCase_sumset_polynomial

/-- info: 'Frontier.AdditiveSweep.ncard_le_of_small_sides' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.AdditiveSweep.ncard_le_of_small_sides

/-- info: 'Frontier.AdditiveSweep.Coherent.add_injOn' does not depend on any axioms -/
#guard_msgs in
#print axioms Frontier.AdditiveSweep.Coherent.add_injOn

/-- info: 'Frontier.AdditiveSweep.abs_sumOn_le_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.AdditiveSweep.abs_sumOn_le_of_budget

/-- info: 'Frontier.agreement_le_of_output_biases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.agreement_le_of_output_biases

/-- info: 'Frontier.FlatSumsetBias.additiveBudget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.FlatSumsetBias.additiveBudget

/-- info: 'Frontier.agreement_le_of_additive_sweeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.agreement_le_of_additive_sweeps

/-- info: 'Frontier.LinearObservation.ncard_mixedFiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearObservation.ncard_mixedFiber

/-- info: 'Frontier.LinearObservation.pow_connectivity_le_messages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearObservation.pow_connectivity_le_messages

/-- info: 'Frontier.Compiler.connectivity_le_cutSignals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.connectivity_le_cutSignals

/-- info: 'Frontier.Compiler.exists_cut_ge_pathwidth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.exists_cut_ge_pathwidth

/-- info: 'Frontier.LinearBoundary.sectionEncoding_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.sectionEncoding_injective
