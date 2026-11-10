module

public import TruthCore.Causality.ActualOnlyEuclidean

@[expose] public section

namespace TruthCore.Results.Causality.ActualOnlyEuclidean
open TruthCore.Causality.ActualEuclidean (EuclideanAt)
open TruthCore.Causality.ActualOnlyEuclidean
open TruthCore.Causality.SpineRivalsStageOne.Control (Place)

/-- Local axioms 5 and 4 at `w` give local axiom 5 at every successor of `w`:
both targets are successors of `w` by transitivity at `w`, so Euclidean access
at `w` relates them. -/
theorem euclideanOnSuccessors {W : Type} (frame : TruthCore.Modal.Frame W) (w : W)
    (hEuclidean : EuclideanAt frame w) (hTransitive : TransitiveAt frame w) :
    EuclideanOnSuccessors frame w :=
  fun v hwv a b hva hvb =>
    hEuclidean a b (hTransitive v a hwv hva) (hTransitive v b hwv hvb)

/-- The two surrogate controls, by case analysis. -/
theorem controls : Control.Certificate := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, Or.inl rfl, ?_, ?_⟩⟩
  · intro v z hv hz
    cases v <;> cases z <;> simp_all [TruthCore.Causality.ActualEuclidean.Control.clustered]
  · intro hT
    have h := hT Place.near Place.far (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
    simp [TruthCore.Causality.ActualEuclidean.Control.clustered] at h
  · intro hE
    have h := hE Place.far Place.actual (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    simp [TruthCore.Causality.ActualEuclidean.Control.clustered] at h
  · intro v z hv hz
    cases v <;> cases z <;> simp_all [Control.appendix]
  · intro v z hv hz
    cases v <;> cases z <;> simp_all [Control.appendix]
  · simp [Control.appendix]
  · intro hE
    have h := hE Place.far Place.actual Place.far (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
    simp [Control.appendix] at h

end TruthCore.Results.Causality.ActualOnlyEuclidean
