import TruthCore.Logic.CogitoSubject
namespace TruthCore.Results.Logic.CogitoSubject
open TruthCore.Logic.CogitoSubject

universe u v

/-- From an occurring thought and the open bearer principle, construct a
subject bearing that thought (∃-elimination, then the principle). -/
theorem thinkingSubjectOfThought {Episode : Sort u} {Subject : Sort v}
    (Occurs : Episode → Prop) (Bears : Subject → Episode → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears) :
    SomeThinkingSubject Occurs Bears := by
  obtain ⟨e, he⟩ := hOccurs
  obtain ⟨s, hs⟩ := hBearer e he
  exact ⟨s, e, he, hs⟩

/-- Occurrence alone does not supply a bearer. -/
theorem subjectlessControl : SubjectlessControl := by
  refine ⟨fun _ => True, fun _ _ => False, ⟨(), trivial⟩, ?_⟩
  intro ⟨_, _, _, hs⟩
  exact hs

/-- The bearer principle alone does not supply an occurring thought. -/
theorem noThoughtControl : NoThoughtControl := by
  refine ⟨fun _ => False, fun _ _ => False, ?_, ?_, ?_⟩
  · intro _ he
    exact False.elim he
  · intro ⟨_, he⟩
    exact he
  · intro ⟨_, _, he, _⟩
    exact he

/-- Every subject bears the one occurring episode; `true` and `false` differ. -/
theorem multipleBearersModel : MultipleBearersModel := by
  refine ⟨fun _ => True, fun _ _ => True, ⟨(), trivial⟩, ?_, ?_⟩
  · intro _ _
    exact ⟨true, trivial⟩
  · exact ⟨true, false, (), fun h => Bool.noConfusion h, trivial, trivial, trivial⟩

/-- Compose `thinkingSubjectOfThought` with the open substance principle. -/
theorem substantialSubjectOfThought {Episode : Sort u} {Subject : Sort v}
    (Occurs : Episode → Prop) (Bears : Subject → Episode → Prop)
    (Substance : Subject → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hSubstance : EveryBearerIsSubstance Occurs Bears Substance) :
    SomeSubstantialThinkingSubject Occurs Bears Substance := by
  obtain ⟨s, e, he, hs⟩ := thinkingSubjectOfThought Occurs Bears hOccurs hBearer
  exact ⟨s, e, he, hs, hSubstance s e he hs⟩

/-- One occurring episode, one bearer, and an empty `Substance` predicate. -/
theorem nonSubstantialBearerModel : NonSubstantialBearerModel := by
  refine ⟨fun _ => True, fun _ _ => True, fun _ => False, ⟨(), trivial⟩, ?_, ?_⟩
  · intro _ _
    exact ⟨(), trivial⟩
  · intro ⟨_, _, _, _, hSubstance⟩
    exact hSubstance

end TruthCore.Results.Logic.CogitoSubject
