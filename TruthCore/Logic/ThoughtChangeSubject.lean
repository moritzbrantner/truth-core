import TruthCore.Greek.Aristotle.Physics
import TruthCore.Logic.CogitoSubject

/-!
The Cogito-to-Aristotle bridge, restricted to change rather than all acts
(from #529; consolidated in #532). The existing Physics III.1 reading supplies
a potential subject for a change, but classifying a thought as change remains
a separate open proposition. Occurrence reuses
`TruthCore.Logic.CogitoSubject.ThoughtOccurs`.
-/
namespace TruthCore.Logic.ThoughtChangeSubject

/-- Every selected thought episode is a change in the Physics III.1 sense.
This is not inferred from the occurrence of thought. -/
def ThoughtChangeBridge {Episode : Type}
    (Thought Change : Episode → Prop) : Prop :=
  ∀ e, Thought e → Change e

/-- An occurring thought that is a change is the actuality of a potential
subject, in the restricted Physics III.1 sense. -/
def ThoughtChangeHasPotentialSubject {Episode Subject : Type}
    (Thought Change : Episode → Prop) (Potential : Subject → Prop)
    (QuaPotentialActuality : Episode → Subject → Prop) : Prop :=
  ∃ e s, Thought e ∧ Change e ∧ Potential s ∧ QuaPotentialActuality e s

/-- Omitting the actual thought leaves the other two premises satisfiable
without a subject of an actual thinking change. -/
def NoThoughtControl : Prop :=
  ∃ (Thought Change : Unit → Prop) (Potential : Unit → Prop)
    (QuaPotentialActuality : Unit → Unit → Prop),
    ThoughtChangeBridge Thought Change ∧
    TruthCore.Greek.Aristotle.Physics.ChangeAsActualityOfPotentialReading
      Change Potential QuaPotentialActuality ∧
    ¬ CogitoSubject.ThoughtOccurs Thought ∧
    ¬ ThoughtChangeHasPotentialSubject Thought Change Potential QuaPotentialActuality

/-- An actual thought can remain non-changing while Aristotle's conditional
account of change is satisfied. -/
def NonChangingThoughtControl : Prop :=
  ∃ (Thought Change : Unit → Prop) (Potential : Unit → Prop)
    (QuaPotentialActuality : Unit → Unit → Prop),
    CogitoSubject.ThoughtOccurs Thought ∧
    TruthCore.Greek.Aristotle.Physics.ChangeAsActualityOfPotentialReading
      Change Potential QuaPotentialActuality ∧
    ¬ ThoughtChangeBridge Thought Change ∧
    ¬ ThoughtChangeHasPotentialSubject Thought Change Potential QuaPotentialActuality

/-- Without the Physics III.1 reading, a thought may be called a change while
the potential-subject relation is empty. -/
def UnconstrainedChangeControl : Prop :=
  ∃ (Thought Change : Unit → Prop) (Potential : Unit → Prop)
    (QuaPotentialActuality : Unit → Unit → Prop),
    CogitoSubject.ThoughtOccurs Thought ∧ ThoughtChangeBridge Thought Change ∧
    ¬ TruthCore.Greek.Aristotle.Physics.ChangeAsActualityOfPotentialReading
      Change Potential QuaPotentialActuality ∧
    ¬ ThoughtChangeHasPotentialSubject Thought Change Potential QuaPotentialActuality

/-- Three independent omission controls, not a metaphysical possibility claim. -/
def OmissionControls : Prop :=
  NoThoughtControl ∧ NonChangingThoughtControl ∧ UnconstrainedChangeControl

end TruthCore.Logic.ThoughtChangeSubject
