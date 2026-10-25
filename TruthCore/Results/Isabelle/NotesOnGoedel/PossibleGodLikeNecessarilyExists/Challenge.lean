import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Isabelle.NotesOnGoedel.PossibleGodLikeNecessarilyExists
open TruthCore.Modal (Frame Symmetric)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity GodLike PositiveNecessarilyPositive)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
/-- AFP `GoedelVariantHOML1.thy`, theorem `Th3`: in Gödel's 1970 variant, if
an existing God-like individual possibly exists, one necessarily exists, from
`Ax2a`, `Ax2b`, `Ax3` and the symmetry of accessibility. `Ax4` is not
used. -/
theorem possibleGodLikeNecessarilyExists {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx2b : PositiveNecessarilyPositive F P)
    (hAx3 : NecessaryExistencePositive F ex P)
    (hSym : Symmetric F) :
    PossibleGodLikeNecessarilyExists F ex P := by
  sorry

/-- `Ax1`, `Ax2a`, `Ax2b`, `Ax3` and symmetry hold together in a model with
one world, accessing no world, and one existing individual, where a property
is positive exactly when that individual has it. The premises of
`possibleGodLikeNecessarilyExists` are therefore not inconsistent, unlike the
full axiom set with `Ax4` (`GOEDEL-1970-INCONSISTENT`). Excluded middle decides
`Ax2a` in the model: it is a hypothesis about Lean propositions, not part of
the model. -/
theorem premisesJointlySatisfiable (hEM : ExcludedMiddle) :
    ∃ (World Ind : Type) (F : Frame World) (ex : ExistsAt World Ind)
      (P : Positivity World Ind),
      Nonempty World ∧
      PositiveClosedUnderConjunction P ∧
      PositiveOrNegationPositiveExclusively P ∧
      PositiveNecessarilyPositive F P ∧
      NecessaryExistencePositive F ex P ∧
      Symmetric F := by
  sorry
end TruthCore.Results.Isabelle.NotesOnGoedel.PossibleGodLikeNecessarilyExists
