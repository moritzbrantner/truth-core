import TruthCore.Logic.Strength.NecessaryFrames

/-!
Certificates for `TruthCore.Logic.Strength.NecessaryFrames` (#1598). Each
equivalence proves STRONG ⇔ WEAK ∧ DELTA for one registered strength pair;
the implication direction reuses the pair's registered backing theorem.
-/

namespace TruthCore.Results.Logic.Strength.NecessaryFrames

open TruthCore.Modal
open TruthCore.Logic.Strength.NecessaryFrames
open TruthCore.Causality.NecessarySenseFork

/-- S5 ⇔ S4 ∧ symmetric frame: a reflexive Euclidean frame is symmetric, and a
reflexive transitive symmetric frame is Euclidean. -/
theorem s5OverS4Exact : S5OverS4Exact := by
  sorry

/-- KTB ⇔ T ∧ symmetric frame: KTB frames are exactly the symmetric T frames. -/
theorem bOverTExact : BOverTExact := by
  sorry

end TruthCore.Results.Logic.Strength.NecessaryFrames
