import TruthCore.Modern.Hume.RegularityModels

namespace TruthCore.Results.Modern.Hume.Regularity
open TruthCore.Modern.Hume.Regularity

private theorem noEffect : ¬ Changes (fun u _ : Bool => u) := by
  rintro ⟨u, h⟩
  exact h rfl

private theorem effect : Changes (fun _ x : Bool => x) := by
  exact ⟨false, Bool.noConfusion⟩

private theorem conjunctionFork : Conjunction fork := by
  intro u
  rfl

private theorem confounding : ConfoundingTest := by
  refine ⟨conjunctionFork, Bool.noConfusion, noEffect, ?_⟩
  intro h
  exact noEffect (h fork conjunctionFork)

private theorem direction : DirectionTest := by
  exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, effect, noEffect, noEffect, effect⟩

private theorem temporal : TemporalTest := by
  exact ⟨by decide, by decide, conjunctionFork, noEffect⟩

private theorem coincidence : CoincidenceTest := by
  refine ⟨fun _ h => h, ⟨(false, true), ?_, ?_⟩⟩
  · exact Bool.noConfusion
  · exact Bool.noConfusion

private theorem intervention : InterventionTest := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl⟩, effect, noEffect, ?_⟩
  intro m n h
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    intro hn
    exact hu ((h u false).trans (hn.trans (h u true).symm))
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    intro hm
    exact hu ((h u false).symm.trans (hm.trans (h u true)))

private theorem prediction : PredictionTest := by
  constructor
  · intro cutoff
    refine ⟨fun _ => false, fun n => if n = cutoff then true else false, ?_, ?_⟩
    · intro n hn
      have hne : n ≠ cutoff := Nat.ne_of_lt hn
      simp only [hne, ↓reduceIte]
    · simp only [↓reduceIte]
      exact Bool.noConfusion
  · intro f b h n
    exact h n

private theorem bestSystem : BestSystemTest := by
  refine ⟨fun _ => Iff.rfl, trivial, trivial, rfl, ?_⟩
  intro h
  cases h

private theorem bruteLocal : LocalCausality brute := by
  intro t ht
  exact ⟨.process, ht⟩

private theorem bruteUngrounded : ¬ GroundedTotality brute := by
  rintro ⟨g, h⟩
  cases h

private theorem groundedLocal : LocalCausality grounded := by
  intro t ht
  exact ⟨.process, ht⟩

private theorem boundary : BoundaryTest := by
  refine ⟨⟨bruteLocal, bruteUngrounded⟩, ⟨groundedLocal, ⟨.process, trivial⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro ⟨c, h⟩
    cases h
  · intro s hs
    exact hs .spacetime
  · intro h
    exact bruteUngrounded (h brute bruteLocal)
  · intro h
    exact h grounded groundedLocal ⟨.process, trivial⟩

private theorem answerMaps : AnswerMapTest := by
  refine ⟨?_, ?_, (fun h => h), ⟨trivial, bruteLocal, bruteUngrounded⟩⟩
  · intro q hq h
    cases q with
    | confounding => exact confounding.2.2.2 h.2
    | direction => exact noEffect ((h.2 chain reverseChain direction.1).mp effect)
    | coincidence => exact Bool.noConfusion (h.2 (false, true))
    | intervention => exact confounding.2.2.2 h.2
    | prediction =>
        obtain ⟨f, g, initialAgreement, different⟩ := prediction.1 2
        exact different (h.2 2 f g initialAgreement)
    | grounding => exact hq rfl
  · intro q hq
    cases q with
    | confounding => exact ⟨trivial, confounding⟩
    | direction => exact ⟨trivial, direction⟩
    | coincidence => exact ⟨trivial, coincidence⟩
    | intervention => exact ⟨trivial, intervention⟩
    | prediction => exact ⟨trivial, prediction⟩
    | grounding => exact (hq rfl).elim

theorem checks : Checks := by
  exact ⟨confounding, direction, temporal, coincidence, intervention, prediction,
    bestSystem, boundary, answerMaps⟩

theorem models : ModelChecks := by
  refine ⟨⟨fork, conjunctionFork, Bool.noConfusion⟩,
    ⟨chain, (fun _ => rfl), Bool.noConfusion, effect, noEffect⟩,
    ⟨brute, bruteLocal, bruteUngrounded⟩⟩

end TruthCore.Results.Modern.Hume.Regularity
