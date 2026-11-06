module

public import TruthCore.Logic.AtomismIndependence

@[expose] public section
namespace TruthCore.Results.Logic.AtomismIndependence
open TruthCore.Logic.AtomismIndependence
open TruthCore.Logic.Verificationism.Model

private theorem saturation : SaturationLaw := by
  intro W V F r a hs C
  constructor
  · intro h value
    obtain ⟨w, hw, he⟩ := hs value
    exact he ▸ h w hw
  · intro h w _
    exact h (r w)

private theorem individuals : IndividualVariation := by
  intro i b
  cases i <;> cases b
  all_goals first
    | exact ⟨make false false, trivial, rfl⟩
    | exact ⟨make false true, trivial, rfl⟩
    | exact ⟨make true false, trivial, rfl⟩
    | exact ⟨make true true, trivial, rfl⟩

private theorem pairs : PairwiseVariation := by
  intro i j hne x y
  cases i <;> cases j <;> cases x <;> cases y
  all_goals first
    | exact False.elim (hne rfl)
    | exact ⟨make false false, trivial, rfl, rfl⟩
    | exact ⟨make false true, trivial, rfl, rfl⟩
    | exact ⟨make true false, trivial, rfl, rfl⟩
    | exact ⟨make true true, trivial, rfl, rfl⟩

private theorem controls : IndependenceControls := by
  have notParity : ¬ Parity (false, false, true) := Bool.noConfusion
  refine ⟨individuals, pairs, (fun w _ => w.property), ?_, ?_, ?_, notParity⟩
  · intro hs
    obtain ⟨w, _, he⟩ := hs (false, false, true)
    exact notParity (he ▸ w.property)
  · intro value
    exact ⟨fill value.1 value.2.1 value.2.2 false, trivial, rfl⟩
  · intro h
    exact notParity (h (fill false false true false) trivial)

private theorem xorMeaning (w : World) :
    xorSentence.eval w ↔ Bool.xor (w 0).1 (w 0).2 = true := by
  change (((w 0).1 = true ∧ ¬ (w 0).2 = true) ∨
    (¬ (w 0).1 = true ∧ (w 0).2 = true)) ↔ _
  cases hp : (w 0).1 <;> cases hq : (w 0).2 <;> decide

private theorem thirdReanalysis (w : Constrained) :
    LawSentence.eval w.val (.r 1) ↔ xorSentence.eval w.val := by
  constructor
  · intro h
    exact (xorMeaning w.val).mpr (w.property ▸ h)
  · intro h
    change (reports w.val).2.2 = true
    exact w.property.symm ▸ (xorMeaning w.val).mp h

private theorem selectedReanalysis (a : LawSentence) (h : Selected a) :
    UsesBasis (reanalyze a) ∧
      ∀ w : Constrained, a.eval w.val ↔ (reanalyze a).eval w.val := by
  induction h with
  | first => exact ⟨rfl, fun _ => Iff.rfl⟩
  | second => exact ⟨rfl, fun _ => Iff.rfl⟩
  | third => exact ⟨⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩, thirdReanalysis⟩
  | neg _ ih =>
    refine ⟨ih.1, fun w => ?_⟩
    exact ⟨fun hn h => hn ((ih.2 w).mpr h), fun hn h => hn ((ih.2 w).mp h)⟩
  | conj _ _ ia ib =>
    refine ⟨⟨ia.1, ib.1⟩, fun w => ?_⟩
    exact ⟨fun h => ⟨(ia.2 w).mp h.1, (ib.2 w).mp h.2⟩,
      fun h => ⟨(ia.2 w).mpr h.1, (ib.2 w).mpr h.2⟩⟩
  | disj _ _ ia ib =>
    refine ⟨⟨ia.1, ib.1⟩, fun w => ?_⟩
    exact ⟨fun h => h.elim (fun h => Or.inl ((ia.2 w).mp h))
        (fun h => Or.inr ((ib.2 w).mp h)),
      fun h => h.elim (fun h => Or.inl ((ia.2 w).mpr h))
        (fun h => Or.inr ((ib.2 w).mpr h))⟩

private theorem reanalysis : Reanalysis := by
  refine ⟨?_, selectedReanalysis⟩
  intro value
  exact ⟨make value.1 value.2, trivial, rfl⟩

private theorem scope : ScopeControl := by
  exact ⟨⟨fill false false false true, rfl⟩, ⟨fill false false false false, rfl⟩,
    rfl, rfl, rfl, Bool.noConfusion⟩

theorem checks : Certificate := ⟨saturation, controls, reanalysis, scope⟩

end TruthCore.Results.Logic.AtomismIndependence
