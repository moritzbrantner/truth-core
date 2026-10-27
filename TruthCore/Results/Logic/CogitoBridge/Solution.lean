import TruthCore.Logic.CogitoBridge
namespace TruthCore.Results.Logic.CogitoBridge
open TruthCore.Logic.CogitoBridge

/-- From an actual thought and the independently assumed bearer principle,
construct a witness of a thinking subject. -/
theorem thinkingSubjectOfThought {Episode Subject : Type}
    (Occurs : Episode → Prop) (SubjectOf : Episode → Subject → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs SubjectOf) :
    SomeThinkingSubject Occurs SubjectOf := by
  obtain ⟨e, he⟩ := hOccurs
  obtain ⟨s, hs⟩ := hBearer e he
  exact ⟨e, s, he, hs⟩

/-- Occurrence alone does not supply a bearer. -/
theorem subjectlessControl : SubjectlessControl := by
  refine ⟨fun _ => True, fun _ _ => False, ⟨(), trivial⟩, ?_⟩
  intro ⟨_, _, _, hs⟩
  exact hs

/-- The bearer rule alone does not establish occurrence. -/
theorem noThoughtControl : NoThoughtControl := by
  refine ⟨fun _ => False, fun _ _ => False, ?_, ?_, ?_⟩
  · intro _ he
    exact False.elim he
  · intro ⟨_, he⟩
    exact he
  · intro ⟨_, _, he, _⟩
    exact he

end TruthCore.Results.Logic.CogitoBridge
