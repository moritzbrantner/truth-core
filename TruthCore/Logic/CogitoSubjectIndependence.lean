/-! Cogito subjecthood: separate grammatical first-person reference,
the occurrence of thought, and the ontological bearer principle.
No substantive metaphysical premise is hidden in the definitions. -/
namespace TruthCore.Logic.CogitoSubjectIndependence

/-- An episode occurs; no subject is built into the episode type. -/
def ThoughtOccurs {E : Type} (Occurs : E → Prop) : Prop := ∃ e, Occurs e

/-- Every occurring thought is borne by some subject. -/
def BearerPrinciple {E S : Type} (Occurs : E → Prop)
    (Bears : S → E → Prop) : Prop :=
  ∀ e, Occurs e → ∃ s, Bears s e

/-- Some subject bears an occurring thought. -/
def ThinkingSubjectExists {E S : Type} (Occurs : E → Prop)
    (Bears : S → E → Prop) : Prop :=
  ∃ s e, Occurs e ∧ Bears s e

/-- The Cogito implication with its independent ontological premise. -/
def SubjectInference : Prop :=
  ∀ (E S : Type) (Occurs : E → Prop) (Bears : S → E → Prop),
    ThoughtOccurs Occurs → BearerPrinciple Occurs Bears →
      ThinkingSubjectExists Occurs Bears

/-- Thought occurrence is compatible with no bearer, even with a nonempty
subject carrier. A subjectless-event interpretation is not thereby real. -/
def SubjectlessEpisodeModel : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ ¬ ThinkingSubjectExists Occurs Bears

/-- A token may have a first-person grammatical marker without being borne
by a subject. The grammatical relation is independent of the bearer relation. -/
def FirstPersonWithoutBearerModel : Prop :=
  ∃ (Occurs FirstPerson : Unit → Prop) (Bears : Unit → Unit → Prop),
    ThoughtOccurs Occurs ∧ FirstPerson () ∧
      ¬ ThinkingSubjectExists Occurs Bears

/-- A witness of subjecthood does not yield uniqueness or persistence.
Two distinct subjects may bear the same occurring episode. -/
def MultipleBearersModel : Prop :=
  ∃ (Occurs : Unit → Prop) (Bears : Bool → Unit → Prop),
    ThoughtOccurs Occurs ∧ BearerPrinciple Occurs Bears ∧
    Bears true () ∧ Bears false ()

end TruthCore.Logic.CogitoSubjectIndependence
