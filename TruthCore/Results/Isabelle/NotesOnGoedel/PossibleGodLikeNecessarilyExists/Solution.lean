import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Isabelle.NotesOnGoedel.PossibleGodLikeNecessarilyExists
open TruthCore.Modal (Frame Symmetric)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Isabelle.AFP.GoedelGod (Positivity GodLike PositiveNecessarilyPositive)
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1

/-- AFP `Th1` (`using Ax2a Ax2b Essence_def God_def`). Let `x` be God-like
and have `ψ`. By `Ax2a`, `ψ` or its negation is positive. Not its negation,
since `x`, having every positive property, would lack `ψ`. So `ψ` is
positive, hence necessarily positive (`Ax2b`), so at every accessible world
every God-like individual has `ψ`. Unlike Scott's `T2`, no excluded middle
is needed: `Ax2a` supplies the disjunction. -/
theorem godLikeIsEssence {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx2b : PositiveNecessarilyPositive F P) :
    GodLikeIsEssence F ex P := by
  intro w x hGodLike ψ hψ v hAccess y _ hGodLikeY
  rcases (hAx2a w ψ).1 with hPositive | hNegation
  · exact hGodLikeY ψ (hAx2b w ψ hPositive v hAccess)
  · exact absurd hψ (hGodLike _ hNegation)

/-- AFP `Th2` (`using Ax3 Th1 God_def NecExist_def`). A God-like `x` has
necessary existence, which is positive (`Ax3`), and being God-like is an
essence of `x` (`Th1`), so being God-like is necessarily exemplified by an
existing individual. -/
theorem godLikeImpliesNecessarilyExists {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx3 : NecessaryExistencePositive F ex P)
    (hTh1 : GodLikeIsEssence F ex P) :
    GodLikeImpliesNecessarilyExists F ex P :=
  fun w x hGodLike =>
    hGodLike (NecessaryExistence F ex) (hAx3 w) (GodLike P) (hTh1 w x hGodLike)

/-- AFP `Th3` (`Th2` and `Rsymm`). Let a God-like `x` exist at some `v`
accessible from `w`. By `Th2` at `v` and symmetry, a God-like individual
exists at `w`; by `Th2` at `w`, one exists at every world accessible from
`w`. -/
theorem possibleGodLikeNecessarilyExists {World : Type} {Ind : Type}
    (F : Frame World) (ex : ExistsAt World Ind) (P : Positivity World Ind)
    (hAx2a : PositiveOrNegationPositiveExclusively P)
    (hAx2b : PositiveNecessarilyPositive F P)
    (hAx3 : NecessaryExistencePositive F ex P)
    (hSym : Symmetric F) :
    PossibleGodLikeNecessarilyExists F ex P := by
  have hTh2 := godLikeImpliesNecessarilyExists F ex P hAx3
    (godLikeIsEssence F ex P hAx2a hAx2b)
  intro w ⟨v, hWV, x, _, hGodLike⟩
  obtain ⟨y, _, hGodLikeY⟩ := hTh2 v x hGodLike w (hSym w v hWV)
  exact hTh2 w y hGodLikeY

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
  refine ⟨Unit, Unit, ⟨fun _ _ => False⟩, fun _ _ => True, fun φ w => φ () w,
    ⟨()⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ hφ hψ
    exact ⟨hφ, hψ⟩
  · intro w φ
    exact ⟨(hEM (φ () w)).elim Or.inl Or.inr, fun ⟨hφ, hNot⟩ => hNot hφ⟩
  · intro _ _ _ _ hAccess
    exact hAccess.elim
  · intro _ _ _ _ hAccess
    exact hAccess.elim
  · intro _ _ hAccess
    exact hAccess
end TruthCore.Results.Isabelle.NotesOnGoedel.PossibleGodLikeNecessarilyExists
