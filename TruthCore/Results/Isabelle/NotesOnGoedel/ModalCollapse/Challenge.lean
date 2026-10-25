import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
namespace TruthCore.Results.Isabelle.NotesOnGoedel.ModalCollapse
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity ModalCollapse)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
/-- Modal collapse (the statement of AFP `GoedelGod.thy`, lemma `MC`) from
Gödel's 1970 axioms `Ax2a`, `Ax3` and `Ax4`, on any frame. -/
theorem modalCollapse {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx3 : NecessaryExistencePositive F ex P)
    (hAx4 : PositiveClosedUnderNecessaryInclusion F ex P) :
    ModalCollapse F := by
  sorry
end TruthCore.Results.Isabelle.NotesOnGoedel.ModalCollapse
