import TruthCore.Logic.ThoughtChangeSubject

namespace TruthCore.Results.Logic.ThoughtChangeSubject
open TruthCore.Logic.ThoughtChangeSubject
open TruthCore.Greek.Aristotle.Physics

/-- Transcription/composition of the existing source reading with an explicit,
open thought-as-change bridge and an actual thought witness. -/
theorem thoughtChangeHasSubject {Episode Subject : Type}
    (Thought Change : Episode → Prop) (Potential : Subject → Prop)
    (QuaPotentialActuality : Episode → Subject → Prop)
    (hThought : ActualThought Thought)
    (hBridge : ThoughtChangeBridge Thought Change)
    (hPhysics : ChangeAsActualityOfPotentialReading Change Potential QuaPotentialActuality) :
    ThoughtChangeHasPotentialSubject Thought Change Potential QuaPotentialActuality := by
  obtain ⟨e, he⟩ := hThought
  have hc : Change e := hBridge e he
  obtain ⟨s, hs, hq⟩ := (hPhysics e).mp hc
  exact ⟨e, s, he, hc, hs, hq⟩

private theorem noThought : NoThoughtControl := by
  refine ⟨(fun _ => False), (fun _ => False), (fun _ => False),
    (fun _ _ => False), ?_, ?_, ?_, ?_⟩
  · intro _ h
    exact h.elim
  · intro e
    constructor
    · intro h
      exact h.elim
    · intro h
      obtain ⟨_, hp, _⟩ := h
      exact hp.elim
  · intro h
    obtain ⟨_, ht⟩ := h
    exact ht
  · intro h
    obtain ⟨_, _, ht, _, _, _⟩ := h
    exact ht

private theorem nonChangingThought : NonChangingThoughtControl := by
  refine ⟨(fun _ => True), (fun _ => False), (fun _ => False),
    (fun _ _ => False), ⟨(), trivial⟩, ?_, ?_, ?_⟩
  · intro e
    constructor
    · intro h
      exact h.elim
    · intro h
      obtain ⟨_, hp, _⟩ := h
      exact hp.elim
  · intro h
    exact h () trivial
  · intro h
    obtain ⟨_, _, _, hc, _, _⟩ := h
    exact hc

private theorem unconstrainedChange : UnconstrainedChangeControl := by
  refine ⟨(fun _ => True), (fun _ => True), (fun _ => False),
    (fun _ _ => False), ⟨(), trivial⟩, ?_, ?_, ?_⟩
  · intro _ _
    trivial
  · intro h
    obtain ⟨_, hp, _⟩ := (h ()).mp trivial
    exact hp
  · intro h
    obtain ⟨_, _, _, _, hp, _⟩ := h
    exact hp

/-- Each premise has an independent finite omission model. -/
theorem omissionControls : OmissionControls := by
  exact ⟨noThought, nonChangingThought, unconstrainedChange⟩

end TruthCore.Results.Logic.ThoughtChangeSubject
