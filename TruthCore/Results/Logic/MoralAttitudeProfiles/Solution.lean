module
public import TruthCore.Logic.MoralAttitudeProfiles
@[expose] public section
namespace TruthCore.Results.Logic.MoralAttitudeProfiles
open TruthCore.Logic.MoralAttitudeProfiles

theorem groundingBridge (p : Profile) (h : GroundingStability p) : GroundingImpliesIntervention p := by
  intro s hs
  exact ⟨hs.1, hs.2.1, hs.2.2.1, h s hs.2.2.2⟩

theorem ancestralDirect : AncestralImpliesDirect := by
  intro p s h n hn
  exact h n (.direct hn)

theorem calibrationTruth : CalibrationTruth := by
  intro p h s hs
  cases h with
  | inl hi => exact ((hi s).mp hs).2.2.1
  | inr hg => exact ((hg s).mp hs).2.2.1

private theorem emptyAncestor (a b : Unit) :
    ¬ Ancestor (sample false false false true).ground a b := by
  intro h
  cases h with
  | direct h => cases h
  | step h _ => cases h

private theorem noGround (stable actualTrue : Bool) :
    NoAttitudeAncestor (sample stable false false actualTrue) () := by
  intro n h
  cases h with
  | direct h => cases h
  | step h _ => cases h

theorem controls : Controls := by
  have stable (g a : Bool) : Invariant (sample true g false a) () := by
    intro p _
    exact ⟨fun h => ⟨h.1, Or.inl rfl⟩, fun h => ⟨h.1, Or.inl rfl⟩⟩
  have varies : ¬ Invariant (sample false false false true) () := by
    intro h
    have hh := (h true (Or.inl rfl)).mpr (by exact ⟨rfl, Or.inr rfl⟩)
    cases hh.2 with
    | inl h => cases h
    | inr h => cases h
  have grounded : ¬ NoAttitudeAncestor (sample true true false true) () := by
    intro h
    exact h () (.direct rfl) trivial
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact ⟨trivial, trivial, by exact ⟨rfl, Or.inl rfl⟩, stable true true⟩
  · exact fun h => grounded h.2.2.2
  · exact ⟨trivial, trivial, by exact ⟨rfl, Or.inr rfl⟩, noGround false true⟩
  · exact fun h => varies h.2.2.2
  · exact ⟨trivial, trivial, by exact ⟨rfl, Or.inl rfl⟩, stable false true⟩
  · exact ⟨trivial, trivial, by exact ⟨rfl, Or.inl rfl⟩, noGround true true⟩
  · exact stable false false
  · exact noGround true false
  · intro h; cases h.2.2.1.1
  · constructor
    · intro a ha
      rcases ha with ha | ha
      · cases ha
      · subst a; exact Iff.rfl
    · intro h
      have hh := (h true).mpr (by exact ⟨rfl, Or.inr rfl⟩)
      cases hh.2 with
      | inl h => cases h
      | inr h => cases h
end TruthCore.Results.Logic.MoralAttitudeProfiles
