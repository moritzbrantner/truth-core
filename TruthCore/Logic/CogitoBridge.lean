/-! Cartesian Cogito: an actual thinking episode, its subject, and the
independent bearer bridge. No claim that any actual thought occurs is assumed. -/
namespace TruthCore.Logic.CogitoBridge

/-- There is an occurring thought episode. -/
def ThoughtOccurs {Episode : Type} (Occurs : Episode → Prop) : Prop :=
  ∃ e, Occurs e

/-- Every occurring thought has some subject. This is an open metaphysical
bridge, not a logical axiom or a definition of occurrence. -/
def EveryThoughtHasSubject {Episode Subject : Type}
    (Occurs : Episode → Prop) (SubjectOf : Episode → Subject → Prop) : Prop :=
  ∀ e, Occurs e → ∃ s, SubjectOf e s

/-- At least one subject bears an occurring thought. -/
def SomeThinkingSubject {Episode Subject : Type}
    (Occurs : Episode → Prop) (SubjectOf : Episode → Subject → Prop) : Prop :=
  ∃ e s, Occurs e ∧ SubjectOf e s

/-- A subject is not inferred from occurrence alone: an episode may occur
while the bearer relation is empty. -/
def SubjectlessControl : Prop :=
  ∃ (Occurs : Unit → Prop) (SubjectOf : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ ¬ SomeThinkingSubject Occurs SubjectOf

/-- An empty occurrence interpretation does not yield an actual thinker,
even when the universal bearer condition is vacuously true. -/
def NoThoughtControl : Prop :=
  ∃ (Occurs : Unit → Prop) (SubjectOf : Unit → Unit → Prop),
    EveryThoughtHasSubject Occurs SubjectOf ∧
    ¬ ThoughtOccurs Occurs ∧ ¬ SomeThinkingSubject Occurs SubjectOf

end TruthCore.Logic.CogitoBridge
