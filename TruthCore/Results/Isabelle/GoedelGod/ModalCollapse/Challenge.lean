import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Isabelle.GoedelGod.ModalCollapse
open TruthCore.Modal (Frame Symmetric)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Isabelle.AFP.GoedelGod
/-- AFP `GoedelGod.thy`, lemma `MC` (left unproved there, `oops`): Scott's
axioms entail modal collapse. Whatever is true at a world is necessary there,
from the same premises as `T3`. -/
theorem modalCollapse {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hA1a : NegationPositiveExcludesPositive P)
    (hA1b : NonPositiveHasPositiveNegation P)
    (hA2 : PositiveClosedUnderNecessaryImplication F P)
    (hA3 : GodLikePositive P)
    (hA4 : PositiveNecessarilyPositive F P)
    (hA5 : NecessaryExistencePositive F P)
    (hSym : Symmetric F)
    (hEM : ExcludedMiddle) :
    ModalCollapse F := by
  sorry
end TruthCore.Results.Isabelle.GoedelGod.ModalCollapse
