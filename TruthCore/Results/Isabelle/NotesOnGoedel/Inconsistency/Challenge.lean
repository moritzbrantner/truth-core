import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
namespace TruthCore.Results.Isabelle.NotesOnGoedel.Inconsistency
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
/-- AFP `GoedelVariantHOML1.thy`, theorem `Inconsistency`: Gödel's 1970 axioms
`Ax2a`, `Ax3` and `Ax4` hold in no Kripke model with a world, on any frame. -/
theorem inconsistency {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx3 : NecessaryExistencePositive F ex P)
    (hAx4 : PositiveClosedUnderNecessaryInclusion F ex P) :
    NoWorld World := by
  sorry
end TruthCore.Results.Isabelle.NotesOnGoedel.Inconsistency
