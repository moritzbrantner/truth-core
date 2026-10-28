import TruthCore.Models.WorldIndexedSources
import TruthCore.Results.Causality.WorldSourceRegress.Solution
namespace TruthCore.Results.Causality.WorldIndexedSources
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Modal.ExistenceDegrees
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Causality.WorldSourceRegress
open TruthCore.Logic.Regress
open TruthCore.Models.WorldIndexedSources

theorem checks : JointControl := by
  let rank (w : Fin 3) (x : Bool) : Nat :=
    if w = 0 then (if x = true then 0 else 1)
    else if w = 1 then (if x = false then 0 else 1) else 0
  have hRawWF (w : Fin 3) : WellFounded (model.Causes w) := by
    have hStep : ∀ source target, model.Causes w source target →
        rank w source < rank w target := by
      intro source target he
      rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    exact Subrelation.wf (fun {_ _} he => hStep _ _ he)
      (InvImage.wf (rank w) Nat.lt_wfRel.wf)
  have hActualWF (w : Fin 3) : WellFounded (actualGraph model w).edge := by
    let f : (actualGraph model w).Map (⟨model.Causes w⟩ : Graph Bool) :=
      ⟨Subtype.val, fun {_ _} he => he⟩
    exact f.wellFounded (hRawWF w)
  have hAcyclic : ActualAcyclic model :=
    fun w => ((actualGraph model w).controls_of_wellFounded (hActualWF w)).1
  have hSound : SoundDistinctCauses model := by
    intro w source target he
    rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨Or.inr ⟨rfl, by decide⟩, Or.inl rfl, by decide⟩
    · exact ⟨Or.inl rfl, Or.inr ⟨rfl, by decide⟩, by decide⟩
  have hNec : NecessaryAt model 0 false := fun _ _ => Or.inl rfl
  have onlyFalse (x : Bool) (hx : NecessaryAt model 0 x) : x = false := by
    cases x with
    | false => rfl
    | true =>
      have he := hx 2 True.intro
      rcases he with he | ⟨_, he⟩
      · exact False.elim (Bool.noConfusion he)
      · exact False.elim (he rfl)
  have hUnionEmpty : ∀ source target,
      ¬ UnionNecessarySupport model model.Causes 0 source target := by
    rintro source target ⟨hs, ht, v, hv, he⟩
    rw [onlyFalse source hs, onlyFalse target ht] at he
    rcases he with ⟨_, he, _⟩ | ⟨_, _, he⟩ <;> exact Bool.noConfusion he
  have hUnionWF : WellFoundedUnionNecessarySupport model model.Causes 0 := by
    refine ⟨fun target => Acc.intro target ?_⟩
    intro source he
    exact False.elim (hUnionEmpty source target he)
  have hPotential : OtherDirectedPotentialCause model 0 false := by
    intro v hv y hy hOther
    cases y with
    | false => exact False.elim (hOther rfl)
    | true => exact ⟨1, True.intro, Or.inr ⟨rfl, rfl, rfl⟩⟩
  have hTrue0 : model.ExistsAt 0 true := Or.inr ⟨rfl, by decide⟩
  have hContingent : ContingentAt model 0 true := by
    refine ⟨hTrue0, 2, True.intro, ?_⟩
    rintro (he | ⟨_, he⟩)
    · exact Bool.noConfusion he
    · exact he rfl
  have hIncoming : model.Causes 0 true false := Or.inl ⟨rfl, rfl, rfl⟩
  have hNotBridge : ¬ NoContingentGroundOfNecessary model model.Causes 0 := by
    intro h
    exact Bool.noConfusion (onlyFalse true (h 0 true false hTrue0 hNec hIncoming))
  have hNotNamed : ¬ NamedNecessarilyUnderived model model.Causes 0 false := by
    intro h
    exact h.2.2 0 true hTrue0 hIncoming
  let roots (w : Fin 3) : Set Bool :=
    Subtype.val '' {s : Actual model w | (actualGraph model w).Source s}
  have rootIff (w : Fin 3) (x : Bool) : x ∈ roots w ↔
      model.ExistsAt w x ∧ ¬ ∃ y, model.ExistsAt w y ∧ model.Causes w y x := by
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.property,
        (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff model w s).mp hs⟩
    · rintro ⟨hx, hs⟩
      exact ⟨⟨x, hx⟩,
        (TruthCore.Results.Causality.WorldSourceRegress.actualSource_iff model w _).mpr hs, rfl⟩
  have hRoots0 : roots 0 = {true} := by
    apply Set.ext
    intro x
    rw [rootIff]
    cases x <;> dsimp [model] <;> decide
  have hRoots1 : roots 1 = {false} := by
    apply Set.ext
    intro x
    rw [rootIff]
    cases x <;> dsimp [model] <;> decide
  have hRoots2 : roots 2 = {false} := by
    apply Set.ext
    intro x
    rw [rootIff]
    cases x <;> dsimp [model] <;> decide
  have hNoCommon : ¬ ∃ x : Bool, ∀ w : Fin 3, x ∈ roots w := by
    rintro ⟨x, hx⟩
    have h0 := hx 0
    have h1 := hx 1
    rw [hRoots0] at h0
    rw [hRoots1] at h1
    exact Bool.noConfusion ((Set.mem_singleton_iff.mp h0).symm.trans
      (Set.mem_singleton_iff.mp h1))
  have hStarter : StarterWorlds model = Set.univ := by
    apply Set.ext
    intro w
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨s, _, hs⟩ :=
        ((actualGraph model w).controls_of_wellFounded (hActualWF w)).2.2
          ⟨false, Or.inl rfl⟩
      exact ⟨s, hs⟩
  have hNoRegress : RegressWorlds model = ∅ := by
    apply Set.ext
    intro w
    constructor
    · rintro ⟨x, f, h0, hInj, hStep⟩
      exact (not_acc_iff_exists_descending_chain.mpr ⟨f, h0, hStep⟩)
        ((hActualWF w).apply x)
    · intro h; exact False.elim h
  exact ⟨hSound, hRawWF, hAcyclic, True.intro, hNec, hPotential, hUnionWF,
    hContingent, hIncoming, hNotBridge, hNotNamed, hRoots0, hRoots1, hRoots2,
    hNoCommon, hStarter, hNoRegress⟩
end TruthCore.Results.Causality.WorldIndexedSources
