import TruthCore.Causality.RootWiring
import TruthCore.Results.Causality.Round4Revisited.Solution

/-!
# Root wiring of disconnected Causality results

Eight derivations that make verified Causality conclusions premises of
arguments whose conclusions already lie on the designated root route. The
first two compose the existing Round 4 theorems `inhabitedFromProduction` and
`inhabitedFromPower` with the owner-approved floor commitment instead of its
open halves. The other six turn the conclusion of a recorded rival refutation
into the universal principle the rival denied, on the same predicates; five of
them use excluded middle (a double negation), the Scotist one is constructive.
No premise is discharged that the refutation itself did not discharge, and no
new proposition is introduced.
-/

namespace TruthCore.Results.Causality.RootWiring
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Causality.Round2ExistenceAct
open TruthCore.Causality.CausalPowerConcreteness
open TruthCore.Causality.MeinongianActuality (NoActualityWithoutBeing)
open TruthCore.Causality.AristotelianRivalRefutations
  (NoActAndPotencyInSameRespect NoMovedWithoutPotency)
open TruthCore.Causality.RivalRefutationsRound2
  (NoMovedNotPotentCountertuple NoMoverLinkWithoutCauseLink)
open TruthCore.Causality.Round3CogitoBase (DoubtIsPerformed PerformedDoubtOfThoughtSelfRefuting)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Latin.Aquinas.SummaTheologiae.HumanIntellect (OperationAttribution)
open TruthCore.Logic.CogitoConcrete (EveryBearerExistsAt InhabitedConcreteAt)
open TruthCore.Logic.CogitoEsse (BorneThoughtExercisesIntellect)
open TruthCore.Logic.CogitoSubject (ThoughtOccurs EveryThoughtHasSubject)

/-! ## The floor commitment in the Cogito derivations -/

/-- The Round 4 activity derivation of a concrete inhabitant of `w`, with the
owner-approved commitment (capacity and activity clauses on the same
`concrete`, `Causes` and `w`) in place of its open activity clause. -/
theorem inhabitedFromFloorActivity {W E Episode : Type} (m : Ontic W E)
    (concrete : E → Prop) (hasCausalPower : W → E → Prop) (w : W)
    (Occurs : Episode → Prop) (Bears : E → Episode → Prop)
    (a : OperationAttribution E Episode)
    (hO : ThoughtOccurs Occurs)
    (hB : EveryThoughtHasSubject Occurs Bears)
    (hEx : BorneThoughtExercisesIntellect Occurs Bears a)
    (hProd : IntellectualExerciseProducesAt m a w)
    (hE : EveryBearerExistsAt m Occurs Bears w)
    (hFloor : OwnerCommitmentAt m concrete hasCausalPower w) :
    InhabitedConcreteAt m concrete w := by
  sorry

/-- The Round 4 capacity derivation, with the owner-approved commitment in
place of its open capacity clause. -/
theorem inhabitedFromFloorPower {W E Episode : Type} (m : Ontic W E)
    (concrete : E → Prop) (hasCausalPower : W → E → Prop) (w : W)
    (Occurs : Episode → Prop) (Bears : E → Episode → Prop)
    (a : OperationAttribution E Episode)
    (hO : ThoughtOccurs Occurs)
    (hB : EveryThoughtHasSubject Occurs Bears)
    (hEx : BorneThoughtExercisesIntellect Occurs Bears a)
    (hPow : IntellectualExerciserHasPowerAt a hasCausalPower w)
    (hE : EveryBearerExistsAt m Occurs Bears w)
    (hFloor : OwnerCommitmentAt m concrete hasCausalPower w) :
    InhabitedConcreteAt m concrete w := by
  sorry

/-! ## From rival refutations to the denied principle -/

/-- No thing is in act without being (the Meinongian rival fails), hence, by
excluded middle on `InAct x esse`, whatever is in act in some respect is in act
as to being. -/
theorem actualityOnlyInsofarAsBeingFromRefutation {B R : Type} (InAct : B → R → Prop)
    (esse : R) (hEM : ExcludedMiddle) (hNo : NoActualityWithoutBeing InAct esse) :
    ActualityOnlyInsofarAsBeingReading InAct esse := by
  sorry

/-- The Scotist rival fails: nothing is in act and in potency in one respect,
which is the Prima Via principle read constructively (`¬ ∃` to `∀ ¬`). -/
theorem notActAndPotencyFromRefutation {B R : Type} (InAct InPotency : B → R → Prop)
    (hNo : NoActAndPotencyInSameRespect InAct InPotency) :
    NotActAndPotencyInSameRespectReading InAct InPotency := by
  sorry

/-- The Ash'arite rival fails, hence, by excluded middle on `InPotency x r`,
whatever is moved in a respect is in potency in it. -/
theorem movedOnlyAsInPotencyFromAshariteRefutation {B R : Type}
    (MovedIn InPotency : B → R → Prop) (hEM : ExcludedMiddle)
    (hNo : NoMovedWithoutPotency MovedIn InPotency) :
    MovedOnlyAsInPotencyReading MovedIn InPotency := by
  sorry

/-- The exact moved-not-potent countertuple fails, hence, by excluded middle,
whatever is moved in a respect is in potency in it. -/
theorem movedOnlyAsInPotencyFromCountertupleRefutation {B R : Type}
    (MovedIn InPotency : B → R → Prop) (hEM : ExcludedMiddle)
    (hNo : NoMovedNotPotentCountertuple MovedIn InPotency) :
    MovedOnlyAsInPotencyReading MovedIn InPotency := by
  sorry

/-- The occasionalist rival fails, hence, by excluded middle on
`CausesAsCaused y x`, every per se mover link is a per se cause link. -/
theorem perSeMoverLinkFromOccasionalistRefutation {B : Type}
    (MovesAsMoved CausesAsCaused : B → B → Prop) (hEM : ExcludedMiddle)
    (hNo : NoMoverLinkWithoutCauseLink MovesAsMoved CausesAsCaused) :
    PerSeMoverLinkIsPerSeCauseLinkReading MovesAsMoved CausesAsCaused := by
  sorry

/-- Some doubt whether thought occurs is performed; by the retorsion its content
'no thought episode occurs' is then false; by excluded middle some thought
episode occurs. -/
theorem thoughtOccursFromRetorsion {Act Episode : Type}
    (Performed DoubtsThought : Act → Prop) (Occurs : Episode → Prop)
    (hEM : ExcludedMiddle)
    (hDoubt : DoubtIsPerformed Performed DoubtsThought)
    (hSelf : PerformedDoubtOfThoughtSelfRefuting Performed DoubtsThought Occurs) :
    ThoughtOccurs Occurs := by
  sorry

/-! ## Controls -/

open TruthCore.Causality.RootWiring.Control
open TruthCore.Causality.Round2ExistenceAct.Control (ont att)

/-- The batch controls: one omission model for the carrying premise of each
derivation and one joint nonvacuity witness. -/
theorem controls : Certificate := by
  sorry

end TruthCore.Results.Causality.RootWiring
