import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Isabelle.GoedelGod.GodLikeNecessarilyExists
open TruthCore.Modal (Frame Symmetric)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Isabelle.AFP.GoedelGod
/-- AFP `GoedelGod.thy`, theorem `T3`: in Scott's variant, necessarily a
God-like being exists, from axioms `A1a`, `A1b`, `A2`, `A3`, `A4`, `A5`, the
symmetry of accessibility (`sym`, modal logic KB) and the classicality of the
host logic (excluded middle). -/
theorem godLikeNecessarilyExists {World : Type} {Ind : Type}
    (F : Frame World) (P : Positivity World Ind)
    (hA1a : NegationPositiveExcludesPositive P)
    (hA1b : NonPositiveHasPositiveNegation P)
    (hA2 : PositiveClosedUnderNecessaryImplication F P)
    (hA3 : GodLikePositive P)
    (hA4 : PositiveNecessarilyPositive F P)
    (hA5 : NecessaryExistencePositive F P)
    (hSym : Symmetric F)
    (hEM : ExcludedMiddle) :
    GodLikeNecessarilyExists F P := by
  sorry

/-- The modal premises of `godLikeNecessarilyExists` hold together in a model
with one world and one individual, so the result does not follow from
inconsistent premises. Excluded middle is not part of the model: it is a
claim about Lean propositions, not about the model. -/
theorem premisesJointlySatisfiable :
    ∃ (World Ind : Type) (F : Frame World) (P : Positivity World Ind),
      NegationPositiveExcludesPositive P ∧
      NonPositiveHasPositiveNegation P ∧
      PositiveClosedUnderNecessaryImplication F P ∧
      GodLikePositive P ∧
      PositiveNecessarilyPositive F P ∧
      NecessaryExistencePositive F P ∧
      Symmetric F := by
  sorry
end TruthCore.Results.Isabelle.GoedelGod.GodLikeNecessarilyExists
