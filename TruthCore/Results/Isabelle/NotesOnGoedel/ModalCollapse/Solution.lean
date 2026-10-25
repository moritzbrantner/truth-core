import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
import TruthCore.Results.Isabelle.NotesOnGoedel.Inconsistency.Solution
namespace TruthCore.Results.Isabelle.NotesOnGoedel.ModalCollapse
open TruthCore.Modal (Frame)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity ModalCollapse)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
open TruthCore.Results.Isabelle.NotesOnGoedel.Inconsistency (inconsistency)

/-- By explosion: a model of `Ax2a`, `Ax3` and `Ax4` has no world
(`inconsistency`), so modal collapse holds at each of its worlds vacuously.
Unlike Scott's modal collapse, this uses nothing about God-likeness. -/
theorem modalCollapse {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx3 : NecessaryExistencePositive F ex P)
    (hAx4 : PositiveClosedUnderNecessaryInclusion F ex P) :
    ModalCollapse F :=
  fun w => (inconsistency F ex P hAx2a hAx3 hAx4 w).elim
end TruthCore.Results.Isabelle.NotesOnGoedel.ModalCollapse
