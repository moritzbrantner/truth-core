import TruthCore.Logic.CogitoSubject
namespace TruthCore.Results.Logic.CogitoSubject
open TruthCore.Logic.CogitoSubject

universe u v

theorem thinkingSubjectOfThought {Episode : Sort u} {Subject : Sort v}
    (Occurs : Episode → Prop) (Bears : Subject → Episode → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears) :
    SomeThinkingSubject Occurs Bears := by
  sorry

theorem subjectlessControl : SubjectlessControl := by
  sorry

theorem noThoughtControl : NoThoughtControl := by
  sorry

theorem multipleBearersModel : MultipleBearersModel := by
  sorry

theorem substantialSubjectOfThought {Episode : Sort u} {Subject : Sort v}
    (Occurs : Episode → Prop) (Bears : Subject → Episode → Prop)
    (Substance : Subject → Prop)
    (hOccurs : ThoughtOccurs Occurs)
    (hBearer : EveryThoughtHasSubject Occurs Bears)
    (hSubstance : EveryBearerIsSubstance Occurs Bears Substance) :
    SomeSubstantialThinkingSubject Occurs Bears Substance := by
  sorry

theorem nonSubstantialBearerModel : NonSubstantialBearerModel := by
  sorry

end TruthCore.Results.Logic.CogitoSubject
