import TruthCore.Alternatives.McTaggart
import TruthCore.Comparison.McTaggart
import TruthCore.Logic.PerformedDenial

/-!
Global underminers as instances of the performed-denial retorsion (#515).

The schema is #516's `TruthCore.Logic.PerformedDenial`: no occurring episode
accurately denies that any episode of its own sort occurs
(`AccurateDenialImpossible`, result `LOGIC-PERFORMED-DENIAL-RETORSION`). What a
global underminer adds is the **presupposition link**: every performance
(asserting, opining, appearing) is itself an occurring episode of the sort its
thesis denies. `PresuppositionLink` states it once; each instance names its
performance, episode sort and token, and the link is that instance's open
premise. The schema never supplies it.

* The Eleatic thesis that nothing is moved (Aristotle, *Physics* VIII.3,
  254a27-30) is an instance: episodes are pairs of a being and a respect, an
  episode occurs when that being is moved in that respect, and the token of an
  opining is the opiner in the respect of that opinion. Its link is exactly
  `OpiningIsBeingMovedReading` (`STMT-OPINION-IS-A-MOTION`), an open premise.
* McTaggart escapes by rejecting the link: his answer (*The Nature of
  Existence* II, § 511, `AppearingsDoNotChangeReading`) has appearings occur
  without being change episodes, and the `opinionGate` model of
  `TruthCore.Alternatives.FirstClosure` satisfies his held position.
-/

namespace TruthCore.Alternatives.Retorsion

open TruthCore.Logic.PerformedDenial
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.McTaggart

/-- The presupposition link of a retorsion instance: every performance of any
content by any agent is, through `token`, an occurring episode of the denied
sort. -/
def PresuppositionLink {Agent Episode : Type} (Performs : Agent → Prop → Prop)
    (Occurs : Episode → Prop) (token : Agent → Prop → Episode) : Prop :=
  ∀ a p, Performs a p → Occurs (token a p)

/-- Eleatic episodes: a being is moved in a respect. -/
def eleaticOccurs {Being Respect : Type} (MovedIn : Being → Respect → Prop) :
    Being × Respect → Prop :=
  fun w => MovedIn w.1 w.2

/-- The token of an opining: the opiner, in the respect of that opinion. -/
def opinionToken {Being Respect : Type} (asOpinion : Prop → Respect) :
    Being → Prop → Being × Respect :=
  fun a p => (a, asOpinion p)

/-- An Eleatic denial episode: the opiner of the thesis that nothing is moved,
in the respect of that opinion. Says nothing about whether it occurs. -/
def eleaticDenies {Being Respect : Type} (MovedIn : Being → Respect → Prop)
    (Opines : Being → Prop → Prop) (asOpinion : Prop → Respect) :
    Being × Respect → Prop :=
  fun w => ∃ x, w = opinionToken asOpinion x (NothingIsMovedReading MovedIn) ∧
    Opines x (NothingIsMovedReading MovedIn)

/-- The Eleatic presupposition link is `OpiningIsBeingMovedReading`. -/
theorem eleatic_link_iff {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (Opines : Being → Prop → Prop)
    (asOpinion : Prop → Respect) :
    PresuppositionLink Opines (eleaticOccurs MovedIn) (opinionToken asOpinion) ↔
      OpiningIsBeingMovedReading MovedIn Opines asOpinion :=
  Iff.rfl

/-- The Eleatic thesis says that no Eleatic episode occurs. -/
theorem nothingIsMoved_noEpisodeOccurs {Being Respect : Type}
    {MovedIn : Being → Respect → Prop} (h : NothingIsMovedReading MovedIn) :
    NoEpisodeOccurs (eleaticOccurs MovedIn) :=
  fun ⟨w, hw⟩ => h w.1 w.2 hw

/-- The Eleatic retorsion as a conditional instance of the performed-denial
schema: if opining is being moved in the respect of that opinion (the link)
and someone opines that nothing is moved, it is not the case that nothing is
moved. -/
def EleaticRetorsionInstance : Prop :=
  ∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
    (Opines : Being → Prop → Prop) (asOpinion : Prop → Respect),
    OpiningIsBeingMovedReading MovedIn Opines asOpinion →
      EleaticThesisIsOpinedReading MovedIn Opines → EleaticThesisFalse MovedIn

/-- McTaggart's change link: every appearing is a change of the appearer. The
presupposition link with episodes the beings themselves, an episode occurring
when that being changes, and the appearer as token. -/
def AppearingIsChangeLink {Being : Type} (Opines : Being → Prop → Prop)
    (Changes : Being → Prop) : Prop :=
  PresuppositionLink Opines Changes (fun a _ => a)

/-- McTaggart escapes the performed-denial retorsion, exactly at the
presupposition link.

1. His § 511 answer `AppearingsDoNotChangeReading` denies the change link
   outright: there are appearings and no appearer changes.
2. With the open, unattributed bridge `MotionIsChangeReading`, it also denies
   the Eleatic link (`appearingsDoNotChange_denies_opinionIsMotion`).
3. The escape is consistent: one model (that of `FirstClosure.opinionGate`)
   satisfies his 1908 bundle, his § 511 answer and the bridge; in it someone
   opines that nothing is moved and someone opines that nothing changes, both
   theses are true, and both links fail. So his appearings occur without being
   episodes of the denied sort, and #516's theorem does not reach him.
4. #516's `StaticEpisodeControl`: occurrence of an episode alone does not
   entail variation of its state.

The model is not claimed to be faithful to McTaggart; it shows only that the
listed commitments do not entail either link. -/
def McTaggartEscapesRetorsion : Prop :=
  (∀ (Being : Type) (Opines : Being → Prop → Prop) (Changes : Being → Prop),
      AppearingsDoNotChangeReading Opines Changes → ¬ AppearingIsChangeLink Opines Changes) ∧
  (∀ (Being Respect : Type) (MovedIn : Being → Respect → Prop)
      (Opines : Being → Prop → Prop) (Changes : Being → Prop) (asOpinion : Prop → Respect),
      AppearingsDoNotChangeReading Opines Changes → MotionIsChangeReading MovedIn Changes →
        ¬ PresuppositionLink Opines (eleaticOccurs MovedIn) (opinionToken asOpinion)) ∧
  (∃ (MovedIn : Unit → Unit → Prop) (Opines : Unit → Prop → Prop)
      (Changes ASeriesChanges : Unit → Prop),
      TruthCore.Comparison.McTaggart.UnrealityOfTime ASeriesChanges Opines Changes ∧
      AppearingsDoNotChangeReading Opines Changes ∧
      MotionIsChangeReading MovedIn Changes ∧
      EleaticThesisIsOpinedReading MovedIn Opines ∧ NothingIsMovedReading MovedIn ∧
      (∃ x, Opines x (NoEpisodeOccurs Changes)) ∧ NoEpisodeOccurs Changes ∧
      ¬ AppearingIsChangeLink Opines Changes ∧
      ∀ asOpinion : Prop → Unit,
        ¬ PresuppositionLink Opines (eleaticOccurs MovedIn) (opinionToken asOpinion)) ∧
  StaticEpisodeControl

end TruthCore.Alternatives.Retorsion
