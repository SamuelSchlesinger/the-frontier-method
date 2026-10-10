import Frontier

/-!
Audit the principal theorem dependencies. Each guard fails if Lean reports an axiom list
different from the standard three below, including a dependency on `sorryAx`.
Run after `lake build --wfail` with `lake env lean scripts/Audit.lean`.
-/

/-- info: 'Frontier.RectangleBias.rectangleFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.RectangleBias.rectangleFree

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

/-- info: 'Frontier.Sweep.ncard_le_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.ncard_le_charged

/-- info: 'Frontier.Sweep.ncard_le_charged_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.ncard_le_charged_codes

/-- info: 'Frontier.SumsetFree.inputGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.SumsetFree.inputGraph

/-- info: 'Frontier.AdditiveSweep.ncard_le_inputGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.AdditiveSweep.ncard_le_inputGraph

/-- info: 'Frontier.lowerBound_sumsetDisperser_freeBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_sumsetDisperser_freeBasis

/-- info: 'Frontier.Sweep.transitionCount_restrictHom_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.transitionCount_restrictHom_le

/-- info: 'Frontier.Sweep.transitionCount_restrictLinear_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.transitionCount_restrictLinear_le

/-- info: 'Frontier.ncard_le_parity_sweep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ncard_le_parity_sweep

/-- info: 'Frontier.ncard_le_parity_joint_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ncard_le_parity_joint_codes

/-- info: 'Frontier.Network.mem_accepted_restrictRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Network.mem_accepted_restrictRead

/-- info: 'Frontier.Network.transitionCount_sweep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Network.transitionCount_sweep_le

/-- info: 'Frontier.SumsetFree.image_addHom_of_saturated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.SumsetFree.image_addHom_of_saturated

/-- info: 'Frontier.pow_sub_read_rank_lt_of_linear_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.pow_sub_read_rank_lt_of_linear_inputs

/-- info: 'Frontier.LinearBoundary.ncard_sub_coordinateRank_le_codim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.ncard_sub_coordinateRank_le_codim

/-- info: 'Frontier.ncard_le_linear_sweep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ncard_le_linear_sweep

/-- info: 'Frontier.Network.ncard_le_of_linear_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Network.ncard_le_of_linear_inputs

/-- info: 'Frontier.cycleRank_add_redundancy_le_of_linear_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.cycleRank_add_redundancy_le_of_linear_inputs

/-- info: 'Frontier.logb_ncard_le_of_linear_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.logb_ncard_le_of_linear_inputs

/-- info: 'Frontier.lowerBound_of_graph_with_redundancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_of_graph_with_redundancy

/-- info: 'Frontier.lowerBound_linear_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_linear_inputs

/-- info: 'Frontier.lowerBound_linear_inputs_of_sublinear_redundancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_linear_inputs_of_sublinear_redundancy

/-- info: 'Frontier.lowerBound_linear_inputs_of_sublinear_codimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_linear_inputs_of_sublinear_codimension

/-- info: 'Frontier.exists_linear_redundancy_rate_preserving_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.exists_linear_redundancy_rate_preserving_gaussian

/-- info: 'Frontier.exists_free_parity_rate_preserving_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.exists_free_parity_rate_preserving_gaussian

/-- info: 'Frontier.Multigraph.Compression.oneSource_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.Compression.oneSource_acyclic

/-- info: 'Frontier.Compiler.topologicalRank_src_lt_tgt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.topologicalRank_src_lt_tgt

/-- info: 'Frontier.Compiler.card_le_twice_oneSource_add_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.card_le_twice_oneSource_add_inputs

/-- info: 'Frontier.Compiler.oneSource_determines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.oneSource_determines

/-- info: 'Frontier.Compiler.oneSource_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.oneSource_xor

/-- info: 'Frontier.Compiler.ncard_boundaryPatterns_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.ncard_boundaryPatterns_le

/-- info: 'Frontier.Compiler.ncard_image_le_oneSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Compiler.ncard_image_le_oneSource

/-- info: 'Frontier.lowerBound_linear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_linear

/-- info: 'Frontier.arith_cauchy_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.arith_cauchy_gaussian

/-- info: 'Frontier.Arithmetic.hessian_determinant_permutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.hessian_determinant_permutation

/-- info: 'Frontier.Arithmetic.mem_vars_determinant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.mem_vars_determinant

/-- info: 'Frontier.Arithmetic.DeterminantMatching.exists_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.DeterminantMatching.exists_crossing

/-- info: 'Frontier.Arithmetic.crossing_le_mixedRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.crossing_le_mixedRank

/-- info: 'Frontier.Arithmetic.hessianDemand_determinant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.hessianDemand_determinant

/-- info: 'Frontier.Arithmetic.lowerBound_determinant_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.lowerBound_determinant_gaussian

/-- info: 'Frontier.Arithmetic.rank_mixedHessian_le_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.rank_mixedHessian_le_cut

/-- info: 'Frontier.Arithmetic.hessian_gate_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.hessian_gate_bound

/-- info: 'Frontier.Arithmetic.lowerBound_hessian_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Arithmetic.lowerBound_hessian_gaussian

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

/-- info: 'Frontier.CubicLayoutBound.exists_layout_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.CubicLayoutBound.exists_layout_log

/-- info: 'Frontier.exists_graph_of_nondeterministic_decides_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.exists_graph_of_nondeterministic_decides_witnesses

/-- info: 'Frontier.lowerBound_nondeterministic_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_nondeterministic_witnesses

/-- info: 'Frontier.lowerBound_nondeterministic_witnesses_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_nondeterministic_witnesses_gaussian

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

/-- info: 'Frontier.Randomized.average_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Randomized.average_le

/-- info: 'Frontier.Randomized.exists_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Randomized.exists_seed

/-- info: 'Frontier.Randomized.success_le_of_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Randomized.success_le_of_class

/-- info: 'Frontier.Randomized.exists_input_success_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Randomized.exists_input_success_le

/-- info: 'Frontier.Randomized.exists_seed_success_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Randomized.exists_seed_success_ge

/-- info: 'Cslib.Circuits.Circuit.eval_fixInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Circuit.eval_fixInputs

/-- info: 'Cslib.Circuits.Circuit.innerSize_fixInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Circuits.Circuit.innerSize_fixInputs

/-- info: 'Frontier.randomized_circuit_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.randomized_circuit_bound

/-- info: 'Frontier.size_lt_of_randomized_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.size_lt_of_randomized_correct

/-- info: 'Frontier.averageCase_randomized_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.averageCase_randomized_gaussian

/-- info: 'Frontier.lowerBound_randomized_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_randomized_gaussian

/-- info: 'Frontier.averageCase_randomized_sumset_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.averageCase_randomized_sumset_polynomial

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

/-- info: 'Frontier.LinearBoundary.ker_jointObservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.ker_jointObservation

/-- info: 'Frontier.LinearBoundary.finrank_jointObservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.finrank_jointObservation

/-- info: 'Frontier.LinearBoundary.ncard_jointObservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.ncard_jointObservation

/-- info: 'Frontier.LinearBoundary.ncard_affine_jointObservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.ncard_affine_jointObservation

/-- info: 'Frontier.Sweep.transitionCount_restrictLinear_le_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.transitionCount_restrictLinear_le_joint

/-- info: 'Frontier.ForestBoundary.compatible_xor_of_one_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ForestBoundary.compatible_xor_of_one_bit

/-- info: 'Frontier.ForestBoundary.exists_bijective_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ForestBoundary.exists_bijective_restrict

/-- info: 'Frontier.ForestBoundary.ncard_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ForestBoundary.ncard_compatible

/-- info: 'Frontier.ForestBoundary.finrank_incident_differences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ForestBoundary.finrank_incident_differences

/-- info: 'Frontier.ForestBoundary.ncard_le_incident' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ForestBoundary.ncard_le_incident

/-- info: 'Frontier.ForestBoundary.ncard_le_incident_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.ForestBoundary.ncard_le_incident_xor

/-- info: 'Frontier.Sweep.transitionCount_le_forest_codes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Sweep.transitionCount_le_forest_codes

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

/-- info: 'Frontier.Communication.rootPotential_min_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Communication.rootPotential_min_le

/-- info: 'Frontier.Network.abs_sumOn_accepted_le_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Network.abs_sumOn_accepted_le_tree

/-- info: 'Frontier.LocalLayout.cutSize_improve_cubic_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LocalLayout.cutSize_improve_cubic_le

/-- info: 'Frontier.PatchLayout.exists_key_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PatchLayout.exists_key_minimum

/-- info: 'Frontier.PatchLayout.card_ties_le_of_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PatchLayout.card_ties_le_of_local

/-- info: 'Frontier.Gaussian.integral_twoVertexGaussianCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.integral_twoVertexGaussianCost_le

/-- info: 'Frontier.Gaussian.exists_twoVertexTreeModel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_twoVertexTreeModel

/-- info: 'Frontier.Gaussian.twoVertexTreeBound_lt_two_mul_gaussianCoefficient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.twoVertexTreeBound_lt_two_mul_gaussianCoefficient

/-- info: 'Frontier.Gaussian.gaussPi_map_forms_eq_of_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.gaussPi_map_forms_eq_of_gram

/-- info: 'Frontier.Gaussian.integral_twoVertexCost_le_of_tree_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.integral_twoVertexCost_le_of_tree_gram

/-- info: 'Frontier.Gaussian.criticalStarGram_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.criticalStarGram_stable

/-- info: 'Frontier.Gaussian.integral_criticalStarPort_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.integral_criticalStarPort_cost_le

/-- info: 'Frontier.Gaussian.sum_unitKernel_edgeRatioError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.sum_unitKernel_edgeRatioError_le

/-- info: 'Frontier.Gaussian.sum_unitKernel_criticalRatioError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.sum_unitKernel_criticalRatioError_le

/-- info: 'Frontier.Gaussian.exists_criticalStarRows_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_criticalStarRows_near

/-- info: 'Frontier.Gaussian.criticalStarGram_stable_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.criticalStarGram_stable_approx

/-- info: 'Frontier.Gaussian.unitKernel_criticalStarGram_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.unitKernel_criticalStarGram_le

/-- info: 'Frontier.PairLayout.twoVertexEnergy_pairKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.twoVertexEnergy_pairKey

/-- info: 'Frontier.Multigraph.portCut_eq_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.portCut_eq_blocks

/-- info: 'Frontier.Multigraph.cutSize_le_portCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.cutSize_le_portCut

/-- info: 'Frontier.PairLayout.exists_key_of_portCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_key_of_portCut

/-- info: 'Frontier.Gaussian.sum_reconstructedStar_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.sum_reconstructedStar_sq_le

/-- info: 'Frontier.Gaussian.unitKernel_critical_star_residual_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.unitKernel_critical_star_residual_le

/-- info: 'Frontier.Gaussian.unitKernel_criticalStarGram_le_of_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.unitKernel_criticalStarGram_le_of_gaps

/-- info: 'Frontier.Gaussian.sum_arccos_star_le_of_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.sum_arccos_star_le_of_average

/-- info: 'Frontier.Gaussian.measureReal_straddleEvent_le_of_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.measureReal_straddleEvent_le_of_average

/-- info: 'Frontier.Gaussian.exists_good_sample_of_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_good_sample_of_mean

/-- info: 'Frontier.Gaussian.measureReal_straddleEvent_add_gap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.measureReal_straddleEvent_add_gap_le

/-- info: 'Frontier.Gaussian.exists_good_sample_with_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_good_sample_with_gap

/-- info: 'Frontier.PairLayout.exists_matching_small_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_matching_small_gap

/-- info: 'Frontier.Gaussian.gap_layout_or_small_gap_matching' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.gap_layout_or_small_gap_matching

/-- info: 'Frontier.Gaussian.integral_twoVertexThresholdCost_le_of_correlation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.integral_twoVertexThresholdCost_le_of_correlation

/-- info: 'Frontier.Gaussian.exists_twoVertexThresholdCost_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_twoVertexThresholdCost_tolerance

/-- info: 'Frontier.Gaussian.exists_twoVertexTree_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_twoVertexTree_tolerance

/-- info: 'Frontier.Gaussian.exists_twoVertexTree_saving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_twoVertexTree_saving

/-- info: 'Frontier.Gaussian.exists_unitKernel_pair_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_unitKernel_pair_tolerance

/-- info: 'Frontier.Gaussian.exists_unitKernel_pair_gap_tolerance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_unitKernel_pair_gap_tolerance

/-- info: 'Frontier.Gaussian.exists_pair_kernel_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.exists_pair_kernel_parameters

/-- info: 'Frontier.Hypergraph.exists_key_patch_cut_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Hypergraph.exists_key_patch_cut_le

/-- info: 'Frontier.LinearBoundary.syndromeRank_submodular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.syndromeRank_submodular

/-- info: 'Frontier.LinearBoundary.finrank_partialSyndrome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.LinearBoundary.finrank_partialSyndrome

/-- info: 'Frontier.Hypergraph.exists_key_patch_syndrome_minimum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Hypergraph.exists_key_patch_syndrome_minimum

/-- info: 'Frontier.Decomposable.ncard_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Decomposable.ncard_le

/-- info: 'Frontier.Gaussian.sum_unitKernel_mul_ge_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.sum_unitKernel_mul_ge_degree

/-- info: 'Frontier.Gaussian.multigraph_vertexLayout_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.multigraph_vertexLayout_bound

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

/-- info: 'Frontier.lowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound

/-- info: 'Frontier.lowerBound_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_four

/-- info: 'Frontier.layoutBound_one_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.layoutBound_one_third

/-- info: 'Frontier.lowerBound_mds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_mds

/-- info: 'Frontier.linear_finite_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.linear_finite_gaussian

/-- info: 'Frontier.linear_polynomial_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.linear_polynomial_gaussian

/-- info: 'Frontier.Decomposable.ncard_le_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Decomposable.ncard_le_size

/-- info: 'Frontier.PairLayout.exists_pair_estimate_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_pair_estimate_parameters

/-- info: 'Frontier.PairLayout.matchingPortCost_matchingKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.matchingPortCost_matchingKey

/-- info: 'Frontier.PairLayout.card_cut_matchingKey_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.card_cut_matchingKey_le

/-- info: 'Frontier.PairLayout.matchingKey_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.matchingKey_source

/-- info: 'Frontier.PairLayout.exists_key_of_matchingCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_key_of_matchingCost

/-- info: 'Frontier.PairLayout.integral_matchingCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.integral_matchingCost

/-- info: 'Frontier.PairLayout.exists_uniform_matching_mean_saving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_uniform_matching_mean_saving

/-- info: 'Frontier.PairLayout.matchingCost_eq_sum_indicators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.matchingCost_eq_sum_indicators

/-- info: 'Frontier.PairLayout.measureReal_matchingCost_deviation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.measureReal_matchingCost_deviation_le

/-- info: 'Frontier.PairLayout.card_cut_le_vertex_grid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.card_cut_le_vertex_grid

/-- info: 'Frontier.PairLayout.exists_key_of_matching_grid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_key_of_matching_grid

/-- info: 'Frontier.PairLayout.exists_matching_sample_of_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_matching_sample_of_mean

/-- info: 'Frontier.PairLayout.exists_matching_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_matching_parameters

/-- info: 'Frontier.PairLayout.exists_cubicLayoutBound_lt_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_cubicLayoutBound_lt_gaussian

/-- info: 'Frontier.exists_layoutBound_lt_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.exists_layoutBound_lt_gaussian

/-- info: 'Frontier.exists_lowerBound_gt_gaussian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.exists_lowerBound_gt_gaussian

/--
info: 'Frontier.Gaussian.integral_twoVertexThresholdCost_le_tree_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Frontier.Gaussian.integral_twoVertexThresholdCost_le_tree_explicit

/-- info: 'Frontier.Gaussian.unitKernel_pair_gap_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Gaussian.unitKernel_pair_gap_explicit

/--
info: 'Frontier.PairLayout.exists_pair_estimate_parameters_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_pair_estimate_parameters_explicit

/-- info: 'Frontier.PairLayout.exists_uniform_matching_mean_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.exists_uniform_matching_mean_explicit

/-- info: 'Frontier.PairLayout.cubicLayoutBound_matching_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.PairLayout.cubicLayoutBound_matching_explicit

/-- info: 'Frontier.layoutBound_matching_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.layoutBound_matching_explicit

/-- info: 'Frontier.matchingCircuitCoefficient_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.matchingCircuitCoefficient_gain

/-- info: 'Frontier.lowerBound_matching_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.lowerBound_matching_explicit

/--
info: 'Frontier.linear_redundancy_rate_preserving_gaussian_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Frontier.linear_redundancy_rate_preserving_gaussian_explicit

/-- info: 'Frontier.free_parity_rate_preserving_gaussian_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.free_parity_rate_preserving_gaussian_explicit
