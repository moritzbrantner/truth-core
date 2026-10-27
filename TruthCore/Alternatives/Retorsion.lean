import TruthCore.Alternatives.McTaggart
import TruthCore.Comparison.McTaggart
import TruthCore.Logic.Retorsion

/-!
Instances of the retorsion schema `TruthCore.Logic.Retorsion` (#515): one
schema instance per global underminer.

* The Eleatic thesis that nothing is moved (Aristotle, *Physics* VIII.3,
  254a27-30) is an instance: witnesses are pairs of a being and a respect, the
  feature is being moved in that respect, and the trace of an opining is the
  opiner in the respect of that opinion. Its presupposition link is exactly
  `OpiningIsBeingMovedReading` (`STMT-OPINION-IS-A-MOTION`), an open premise.
* McTaggart escapes: his answer (*The Nature of Existence* II, § 511,
  `AppearingsDoNotChangeReading`) rejects the presupposition link, not the
  schema's logic, and the `opinionGate` model of
  `TruthCore.Alternatives.FirstClosure` satisfies his held position.
-/

namespace TruthCore.Alternatives.Retorsion

open TruthCore.Logic.Retorsion
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.McTaggart

/-- The Eleatic underminer: opining, being moved in a respect, and the thesis
that nothing is moved. -/
def eleaticUnderminer {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (Opines : Being → Prop → Prop) :
    Underminer Being (Being × Respect) where
  Performs := Opines
  Feature w := MovedIn w.1 w.2
  thesis := NothingIsMovedReading MovedIn
  denies h w := h w.1 w.2

/-- The trace of an opining: the opiner, in the respect of that opinion. -/
def opinionTrace {Being Respect : Type} (asOpinion : Prop → Respect) :
    Being → Prop → Being × Respect :=
  fun a p => (a, asOpinion p)

/-- The Eleatic presupposition link is `OpiningIsBeingMovedReading`. -/
theorem eleatic_link_iff {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (Opines : Being → Prop → Prop)
    (asOpinion : Prop → Respect) :
    (eleaticUnderminer MovedIn Opines).Link (opinionTrace asOpinion) ↔
      OpiningIsBeingMovedReading MovedIn Opines asOpinion :=
  Iff.rfl

/-- The Eleatic retorsion as a conditional schema instance: if opining is a
motion and someone opines that nothing is moved, the Eleatic thesis is false. -/
def EleaticRetorsionInstance : Prop :=
  ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
    (Opines : Being → Prop → Prop) (asOpinion : Prop → Respect),
    OpiningIsBeingMovedReading MovedIn Opines asOpinion →
      EleaticThesisIsOpinedReading MovedIn Opines → EleaticThesisFalse MovedIn

/-- The Eleatic thesis is false, obtained from the retorsion schema. -/
theorem eleaticThesisFalse_of_schema {Being Respect : Type}
    {MovedIn : Being → Respect → Prop} {Opines : Being → Prop → Prop}
    {asOpinion : Prop → Respect}
    (hOpinionIsMotion : OpiningIsBeingMovedReading MovedIn Opines asOpinion)
    (hHeld : EleaticThesisIsOpinedReading MovedIn Opines) :
    EleaticThesisFalse MovedIn :=
  (eleaticUnderminer MovedIn Opines).thesis_false
    (trace := opinionTrace asOpinion) hOpinionIsMotion hHeld

/-- McTaggart's underminer in his own general sense of change: appearing, a
being's changing, and the thesis that nothing changes. The 1908 bundle
`UnrealityOfTime` entails this thesis (`unrealityOfTime_nothingChanges`). -/
def changeUnderminer {Being : Type}
    (Opines : Being → Prop → Prop) (Changes : Being → Prop) : Underminer Being Being where
  Performs := Opines
  Feature := Changes
  thesis := ∀ x, ¬ Changes x
  denies h := h

/-- The trace of an appearing for change: the appearer itself. -/
def appearerTrace {Being : Type} : Being → Prop → Being := fun a _ => a

/-- McTaggart 1908 (no A-series change, and all change is A-series change)
entails the thesis of `changeUnderminer`. -/
theorem unrealityOfTime_nothingChanges {Being : Type}
    {ASeriesChanges : Being → Prop} {Opines : Being → Prop → Prop} {Changes : Being → Prop}
    (h : TruthCore.Comparison.McTaggart.UnrealityOfTime ASeriesChanges Opines Changes) :
    (changeUnderminer Opines Changes).thesis :=
  fun x hx => (h.2 x hx).elim fun e he => h.1.1 e he

/-- McTaggart escapes the schema, and exactly at the presupposition link.

1. His § 511 answer `AppearingsDoNotChangeReading` denies the link of his own
   change instance outright: there are appearings and no appearer changes.
2. With the open, unattributed bridge `MotionIsChangeReading`, it also denies
   the link of the Eleatic instance, for every trace of the form
   `opinionTrace` (this is `appearingsDoNotChange_denies_opinionIsMotion`).
3. The escape is consistent: one model (that of `FirstClosure.opinionGate`)
   satisfies his 1908 bundle, his § 511 answer and the bridge, and in it both
   held positions (Eleatic and change) hold while both links fail. So the
   schema's logic is not what he rejects; nothing in the encoded vocabulary
   forces the link on him.

The model is not claimed to be faithful to McTaggart; it shows only that the
listed commitments do not entail the link. -/
def McTaggartEscapesRetorsion : Prop :=
  (∀ (Being : Type) (Opines : Being → Prop → Prop) (Changes : Being → Prop),
      AppearingsDoNotChangeReading Opines Changes →
        ¬ (changeUnderminer Opines Changes).Link appearerTrace) ∧
  (∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (Opines : Being → Prop → Prop) (Changes : Being → Prop) (asOpinion : Prop → Respect),
      AppearingsDoNotChangeReading Opines Changes → MotionIsChangeReading MovedIn Changes →
        ¬ (eleaticUnderminer MovedIn Opines).Link (opinionTrace asOpinion)) ∧
  (∃ (MovedIn : Unit → Unit → Prop) (Opines : Unit → Prop → Prop)
      (Changes ASeriesChanges : Unit → Prop),
      TruthCore.Comparison.McTaggart.UnrealityOfTime ASeriesChanges Opines Changes ∧
      AppearingsDoNotChangeReading Opines Changes ∧
      MotionIsChangeReading MovedIn Changes ∧
      (changeUnderminer Opines Changes).Position ∧
      (eleaticUnderminer MovedIn Opines).Position ∧
      ¬ (changeUnderminer Opines Changes).Link appearerTrace ∧
      ∀ asOpinion : Prop → Unit,
        ¬ (eleaticUnderminer MovedIn Opines).Link (opinionTrace asOpinion))

end TruthCore.Alternatives.Retorsion
