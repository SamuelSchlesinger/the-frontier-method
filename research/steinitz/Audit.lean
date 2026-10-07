import Frontier.Layouts.Incidence

/-! The incidence obstruction uses only Lean's standard axioms. -/

/-- info: 'Frontier.Multigraph.sum_incidenceVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.sum_incidenceVector

/-- info: 'Frontier.Multigraph.incidenceEnergy_signedIndicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.incidenceEnergy_signedIndicator

/-- info: 'Frontier.Multigraph.exists_signed_incidence_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.exists_signed_incidence_bound_iff

/-- info: 'Frontier.Multigraph.cutSize_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.cutSize_split

/-- info: 'Frontier.Multigraph.cutSize_le_two_mul_max_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Frontier.Multigraph.cutSize_le_two_mul_max_split
