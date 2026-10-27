/-!
Cogito subjecthood, consolidated from #523 and #524 (issue #532). The step from
an occurring thought to a thinking subject is valid only with an explicit,
open bearer principle; the controls show that neither premise suffices alone
and that the principle gives no uniqueness of the bearer. The further step to a
substantial bearer (from #525) needs its own open substance principle.

Source-free and stipulative: no proposition is attributed to Descartes, and no
passage is materialized. `ThoughtOccurs Occurs` is the positive form `∃ e,
Occurs e`; it implies, but is not constructively equivalent to, the negation of
`TruthCore.Logic.PerformedDenial.NoEpisodeOccurs Occurs` (#516). The subject
`s` in `Bears s e` is a bearer only: not a grammatical first person, not a
substance, not an enduring or immaterial self. Nothing here shows that any
thought actually occurs.
-/
namespace TruthCore.Logic.CogitoSubject

universe u v

/-- Some thought episode occurs in the supplied interpretation. `Occurs` is an
unconstrained predicate over a possibly empty episode carrier. -/
def ThoughtOccurs {Episode : Sort u} (Occurs : Episode → Prop) : Prop :=
  ∃ e, Occurs e

/-- The bearer principle: every occurring thought is borne by some subject.
An open metaphysical bridge, not a logical truth or part of `Occurs`. -/
def EveryThoughtHasSubject {Episode : Sort u} {Subject : Sort v}
    (Occurs : Episode → Prop) (Bears : Subject → Episode → Prop) : Prop :=
  ∀ e, Occurs e → ∃ s, Bears s e

/-- Some subject bears some occurring thought. -/
def SomeThinkingSubject {Episode : Sort u} {Subject : Sort v}
    (Occurs : Episode → Prop) (Bears : Subject → Episode → Prop) : Prop :=
  ∃ s e, Occurs e ∧ Bears s e

/-- Omitting the bearer principle: one episode occurs and the bearer relation
is empty. A finite interpretation, not a claim that subjectless thought is
metaphysically possible. -/
def SubjectlessControl : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ ¬ SomeThinkingSubject Occurs Bears

/-- Omitting occurrence: the bearer principle holds (vacuously) while no thought
occurs and no thinking subject exists. -/
def NoThoughtControl : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop),
    EveryThoughtHasSubject Occurs Bears ∧
      ¬ ThoughtOccurs Occurs ∧ ¬ SomeThinkingSubject Occurs Bears

/-- Both premises hold and two distinct subjects bear one occurring episode:
the bearer principle does not make the bearer unique. -/
def MultipleBearersModel : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Bool → Unit → Prop),
    ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      ∃ s₁ s₂ e, s₁ ≠ s₂ ∧ Occurs e ∧ Bears s₁ e ∧ Bears s₂ e

/-- The substance principle (from #525): every bearer of an occurring thought
satisfies `Substance`. A separate open thesis, strictly beyond the bearer
principle. `Substance` is an unconstrained predicate here, not Aristotle's or
Descartes's account of substance. -/
def EveryBearerIsSubstance {Episode : Sort u} {Subject : Sort v}
    (Occurs : Episode → Prop) (Bears : Subject → Episode → Prop)
    (Substance : Subject → Prop) : Prop :=
  ∀ s e, Occurs e → Bears s e → Substance s

/-- Some subject satisfying `Substance` bears some occurring thought. -/
def SomeSubstantialThinkingSubject {Episode : Sort u} {Subject : Sort v}
    (Occurs : Episode → Prop) (Bears : Subject → Episode → Prop)
    (Substance : Subject → Prop) : Prop :=
  ∃ s e, Occurs e ∧ Bears s e ∧ Substance s

/-- Omitting the substance principle: a thought occurs and the bearer principle
holds, but no bearer satisfies `Substance`. A bearer is not thereby a
substance. A finite interpretation only. -/
def NonSubstantialBearerModel : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop) (Substance : Unit → Prop),
    ThoughtOccurs Occurs ∧ EveryThoughtHasSubject Occurs Bears ∧
      ¬ SomeSubstantialThinkingSubject Occurs Bears Substance

end TruthCore.Logic.CogitoSubject
