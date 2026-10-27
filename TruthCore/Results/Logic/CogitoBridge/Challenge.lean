import TruthCore.Logic.CogitoBridge
namespace TruthCore.Results.Logic.CogitoBridge
open TruthCore.Logic.CogitoBridge

theorem thinkingSubjectOfThought {Episode Subject : Type}
    (Occurs : Episode → Prop) (SubjectOf : Episode → Subject → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs SubjectOf) :
    SomeThinkingSubject Occurs SubjectOf := by
  sorry

theorem subjectlessControl : SubjectlessControl := by
  sorry

theorem noThoughtControl : NoThoughtControl := by
  sorry

end TruthCore.Results.Logic.CogitoBridge
