module

public import TruthCore.Logic.AssertionRetorsion

@[expose] public section

namespace TruthCore.Results.Logic.AssertionRetorsion

open TruthCore.Logic.AssertionRetorsion
open TruthCore.Logic.CogitoSubject (ThoughtOccurs)

/-- The same assertion supplies an occurring thought when the cognitive
realization bridge holds. This is the positive Cogito occurrence witness. -/
theorem thoughtFromAssertion {Agent Content Episode : Type}
    (Asserts : Agent → Content → Prop) (claim : Content) (Occurs : Episode → Prop)
    (Realizes : Agent → Content → Episode → Prop)
    (hMade : AssertionMade Asserts claim)
    (hRealizes : AssertionRealized Asserts claim Occurs Realizes) :
    ThoughtOccurs Occurs := by
  obtain ⟨a, ha⟩ := hMade
  obtain ⟨e, he, _⟩ := hRealizes a ha
  exact ⟨e, he⟩

/-- The occurrence and phenomenal bridges apply to one shared episode. -/
theorem experienceFromAssertion {Agent Content Episode : Type}
    (Asserts : Agent → Content → Prop) (claim : Content) (Occurs Experienced : Episode → Prop)
    (Realizes : Agent → Content → Episode → Prop)
    (hMade : AssertionMade Asserts claim)
    (hRealizes : AssertionRealized Asserts claim Occurs Realizes)
    (hPhenomenal : AssertionRealizationsExperienced Asserts claim Occurs Experienced Realizes) :
    ExperienceOccurs Occurs Experienced := by
  obtain ⟨a, ha⟩ := hMade
  obtain ⟨e, he, hre⟩ := hRealizes a ha
  exact ⟨e, he, hPhenomenal a e ha he hre⟩

/-- An occurrence witness and a representation bridge give an existent.
No subject or substance principle is used. -/
theorem existenceFromOccurrence {Episode Being : Type}
    (Occurs : Episode → Prop) (ExistsIn : Being → Prop) (represent : Episode → Being)
    (hOccurs : ThoughtOccurs Occurs)
    (hRepresents : OccurringThoughtIsRepresentedAsExisting Occurs ExistsIn represent) :
    SomeExistent ExistsIn := by
  obtain ⟨e, he⟩ := hOccurs
  exact ⟨represent e, hRepresents e he⟩

/-- The selected assertion supplies a counterexample to the empty-meaning
extension under the local cognitive-meaning bridge. -/
theorem meaningFromAssertion {Agent Content : Type}
    (Asserts : Agent → Content → Prop) (claim : Content) (Meaningful : Content → Prop)
    (hMade : AssertionMade Asserts claim)
    (hMeaning : AssertedContentIsMeaningful Asserts claim Meaningful) :
    SomeMeaningfulContent Meaningful := by
  obtain ⟨a, ha⟩ := hMade
  exact ⟨claim, hMeaning a ha⟩

/-- A sincere assertion of the denial supplies an instance of the very
attitude its content denies. -/
theorem beliefFromSincereDenial {Agent : Type}
    (Asserts Believes : Agent → Prop → Prop)
    (hMade : NoBeliefsIsAsserted Asserts Believes)
    (hSincere : NoBeliefsAssertionIsSincere Asserts Believes) :
    SomeBelief Believes := by
  obtain ⟨a, ha⟩ := hMade
  exact ⟨a, NoBeliefs Believes, hSincere a ha⟩

/-- Small interpretations isolate each bridge from the other displayed inputs. -/
theorem controls : OmissionControls := by
  constructor
  · let Believes : Unit → Prop → Prop := fun _ _ => False
    let aboutDenial : Unit → Prop → Prop := fun _ p => p = NoBeliefs Believes
    refine ⟨aboutDenial, Believes, aboutDenial, ⟨(), rfl⟩, ?_, rfl,
      ⟨(), NoBeliefs Believes, rfl⟩, ?_⟩
    · intro hBelief
      obtain ⟨_, _, h⟩ := hBelief
      exact h
    · intro h
      exact h () rfl
  constructor
  · refine ⟨(fun _ _ => True), (fun _ => False), ⟨(), trivial⟩, ?_, ?_⟩
    · intro hMeaning
      obtain ⟨_, h⟩ := hMeaning
      exact h
    · intro h
      exact h () trivial
  constructor
  · refine ⟨(fun _ _ => True), (fun _ => False), (fun _ _ _ => True),
      ⟨(), trivial⟩, ?_, ?_⟩
    · intro hThought
      obtain ⟨_, h⟩ := hThought
      exact h
    · intro h
      obtain ⟨_, hOccurs, _⟩ := h () trivial
      exact hOccurs
  constructor
  · refine ⟨(fun _ _ => True), (fun _ => True), (fun _ => False), (fun _ => True),
      (fun _ _ _ => True), id, ⟨(), trivial⟩, ?_, ?_, ?_, ?_⟩
    · intro _ _
      exact ⟨(), trivial, trivial⟩
    · intro _ _
      trivial
    · intro hExperience
      obtain ⟨_, _, h⟩ := hExperience
      exact h
    · intro h
      exact h () () trivial trivial trivial
  · refine ⟨(fun _ => True), (fun _ => False), id, ⟨(), trivial⟩, ?_, ?_⟩
    · intro hExistent
      obtain ⟨_, h⟩ := hExistent
      exact h
    · intro h
      exact h () trivial

end TruthCore.Results.Logic.AssertionRetorsion
