module

public import TruthCore.Causality.Round4Revisited
public import TruthCore.Causality.MeinongianActuality
public import TruthCore.Causality.AristotelianRivalRefutations
public import TruthCore.Causality.Round3CogitoBase
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1

/-!
# Root wiring of disconnected Causality results (controls only)

The batch `ROOT-WIRING` (spec `specs/causality-root-wiring.toml`, map
`explorations/causality-root-wiring.toml`) introduces no new proposition. It
composes verified Causality conclusions that no root route consumed with
premises of the designated root route:

* the owner-approved floor commitment `OwnerCommitmentAt`
  (`STMT-CAUSAL-POWER-AND-ACTIVITY-REQUIRE-CONCRETENESS`) replaces its
  activity or capacity half in the two Round 4 Cogito derivations of
  `InhabitedConcreteAt`;
* the conclusions of four rival refutations (Meinongian actuality, Scotist act
  and potency, the Ash'arite and countertuple forms of moved-without-potency,
  occasionalist mover links) yield, with excluded middle where needed, the
  universal principle the rival denied, on the same predicates;
* the Cogito retorsion with a performed doubt yields, with excluded middle,
  that some thought occurs.

This module holds only the batch controls: an omission model for the premise
that carries each derivation, and one joint nonvacuity witness. Excluded
middle is not omitted: it has no finite countermodel in a classical
metatheory. Satisfiability and omission only; no model is claimed to describe
reality.
-/

@[expose] public section

namespace TruthCore.Causality.RootWiring

namespace Control
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.Round2ExistenceAct.Control (ont att)
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.Causality.MeinongianActuality (NoActualityWithoutBeing)
open TruthCore.Causality.AristotelianRivalRefutations
  (NoActAndPotencyInSameRespect NoMovedWithoutPotency)
open TruthCore.Causality.RivalRefutationsRound2
  (NoMovedNotPotentCountertuple NoMoverLinkWithoutCauseLink)
open TruthCore.Causality.Round3CogitoBase (DoubtIsPerformed PerformedDoubtOfThoughtSelfRefuting)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.CogitoConcrete (EveryBearerExistsAt InhabitedConcreteAt)
open TruthCore.Logic.CogitoEsse (BorneThoughtExercisesIntellect)
open TruthCore.Logic.CogitoSubject (ThoughtOccurs EveryThoughtHasSubject)

/-- `inhabitedFromFloorActivity`, omit the floor commitment: the thinking
bearer exists and causes something at `w` but nothing is concrete, so the
activity clause fails and no concrete candidate exists. -/
def omitFloorActivity : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciseProducesAt (ont True True) (att True) () ∧
    EveryBearerExistsAt (ont True True) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    ¬ OwnerCommitmentAt (ont True True) (fun _ => False) (fun (_ _ : Unit) => True) () ∧
    ¬ InhabitedConcreteAt (ont True True) (fun _ => False) ()

/-- `inhabitedFromFloorPower`, omit the floor commitment: the thinking bearer
exists and has causal power at `w` but nothing is concrete. -/
def omitFloorPower : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciserHasPowerAt (att True) (fun (_ _ : Unit) => True) () ∧
    EveryBearerExistsAt (ont True True) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    ¬ OwnerCommitmentAt (ont True True) (fun _ => False) (fun (_ _ : Unit) => True) () ∧
    ¬ InhabitedConcreteAt (ont True True) (fun _ => False) ()

/-- `actualityOnlyInsofarAsBeingFromRefutation`, omit the refutation: one
thing in act in respect `false` but not in the respect `true` read as esse. -/
def omitMeinong : Prop :=
  ¬ NoActualityWithoutBeing (fun (_ : Unit) (r : Bool) => r = false) true ∧
    ¬ ActualityOnlyInsofarAsBeingReading (fun (_ : Unit) (r : Bool) => r = false) true

/-- `notActAndPotencyFromRefutation`, omit the refutation: one thing in act and
in potency in its only respect. -/
def omitScotist : Prop :=
  ¬ NoActAndPotencyInSameRespect (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    ¬ NotActAndPotencyInSameRespectReading (fun (_ _ : Unit) => True) (fun _ _ => True)

/-- `movedOnlyAsInPotencyFromAshariteRefutation`, omit the refutation: one
thing moved without potency. -/
def omitAsharite : Prop :=
  ¬ NoMovedWithoutPotency (fun (_ _ : Unit) => True) (fun _ _ => False) ∧
    ¬ MovedOnlyAsInPotencyReading (fun (_ _ : Unit) => True) (fun _ _ => False)

/-- `movedOnlyAsInPotencyFromCountertupleRefutation`, omit the refutation. -/
def omitCountertuple : Prop :=
  ¬ NoMovedNotPotentCountertuple (fun (_ _ : Unit) => True) (fun _ _ => False) ∧
    ¬ MovedOnlyAsInPotencyReading (fun (_ _ : Unit) => True) (fun _ _ => False)

/-- `perSeMoverLinkFromOccasionalistRefutation`, omit the refutation: one per
se mover link that is no per se cause link. -/
def omitOccasionalist : Prop :=
  ¬ NoMoverLinkWithoutCauseLink (fun (_ _ : Unit) => True) (fun _ _ => False) ∧
    ¬ PerSeMoverLinkIsPerSeCauseLinkReading (fun (_ _ : Unit) => True) (fun _ _ => False)

/-- `thoughtOccursFromRetorsion`, omit the retorsion: a performed doubt with no
occurring thought. -/
def omitRetorsion : Prop :=
  DoubtIsPerformed (fun (_ : Unit) => True) (fun _ => True) ∧
    ¬ PerformedDoubtOfThoughtSelfRefuting (fun (_ : Unit) => True) (fun _ => True)
      (fun (_ : Unit) => False) ∧
    ¬ ThoughtOccurs (fun (_ : Unit) => False)

/-- `thoughtOccursFromRetorsion`, omit the performed doubt: the retorsion holds
vacuously and no thought occurs. -/
def omitDoubtPerformed : Prop :=
  ¬ DoubtIsPerformed (fun (_ : Unit) => False) (fun _ => True) ∧
    PerformedDoubtOfThoughtSelfRefuting (fun (_ : Unit) => False) (fun _ => True)
      (fun (_ : Unit) => False) ∧
    ¬ ThoughtOccurs (fun (_ : Unit) => False)

/-- One joint interpretation in which every premise and conclusion of the eight
derivations holds with populated antecedents: a thinking, existing, causing and
empowered concrete bearer; a being in act in esse; a being in act and a being
moved in potency; a per se mover link that is a per se cause link; and a
performed doubt realized by an occurring thought. -/
def witness : Prop :=
  ThoughtOccurs (fun (_ : Unit) => True) ∧
    EveryThoughtHasSubject (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) ∧
    BorneThoughtExercisesIntellect (fun _ => True) (fun _ _ => True) (att True) ∧
    IntellectualExerciseProducesAt (ont True True) (att True) () ∧
    IntellectualExerciserHasPowerAt (att True) (fun (_ _ : Unit) => True) () ∧
    EveryBearerExistsAt (ont True True) (fun (_ : Unit) => True) (fun (_ _ : Unit) => True) () ∧
    OwnerCommitmentAt (ont True True) (fun _ => True) (fun (_ _ : Unit) => True) () ∧
    InhabitedConcreteAt (ont True True) (fun _ => True) () ∧
    NoActualityWithoutBeing (fun (_ _ : Unit) => True) () ∧
    ActualityOnlyInsofarAsBeingReading (fun (_ _ : Unit) => True) () ∧
    NoActAndPotencyInSameRespect (fun (_ _ : Unit) => True) (fun _ _ => False) ∧
    NotActAndPotencyInSameRespectReading (fun (_ _ : Unit) => True) (fun _ _ => False) ∧
    NoMovedWithoutPotency (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    NoMovedNotPotentCountertuple (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    MovedOnlyAsInPotencyReading (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    NoMoverLinkWithoutCauseLink (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    PerSeMoverLinkIsPerSeCauseLinkReading (fun (_ _ : Unit) => True) (fun _ _ => True) ∧
    DoubtIsPerformed (fun (_ : Unit) => True) (fun _ => True) ∧
    PerformedDoubtOfThoughtSelfRefuting (fun (_ : Unit) => True) (fun _ => True)
      (fun (_ : Unit) => True) ∧
    ThoughtOccurs (fun (_ : Unit) => True)

/-- The batch controls: one omission model for the carrying premise of each
derivation (two for the retorsion) and one joint nonvacuity witness. -/
def Certificate : Prop :=
  omitFloorActivity ∧ omitFloorPower ∧ omitMeinong ∧ omitScotist ∧ omitAsharite ∧
    omitCountertuple ∧ omitOccasionalist ∧ omitRetorsion ∧ omitDoubtPerformed ∧ witness

end Control

end TruthCore.Causality.RootWiring
