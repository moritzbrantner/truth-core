import TruthCore.Isabelle.AFP.NotesOnGoedel.ActualistPossibilityBoundary

namespace TruthCore.Results.Isabelle.NotesOnGoedel.ActualistPossibilityBoundary
open TruthCore.Modal (Frame Symmetric)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity GodLike)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
open TruthCore.Isabelle.AFP.NotesOnGoedel.ActualistPossibilityBoundary

/-- Ax3 and symmetry already make the 1970 Th3 possibility antecedent false.
The partial axiom set can still have worlds; its conditional existence theorem
therefore cannot establish a nonvacuous actualist possibility branch. -/
theorem noPossibleActualistGodLike {World Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx3 : NecessaryExistencePositive F ex P) (hSym : Symmetric F) :
    NoPossibleActualistGodLike F ex P := by
  sorry

end TruthCore.Results.Isabelle.NotesOnGoedel.ActualistPossibilityBoundary
