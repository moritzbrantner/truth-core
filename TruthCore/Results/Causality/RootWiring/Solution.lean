module

public import TruthCore.Causality.RootWiring
public import TruthCore.Results.Causality.Round4Revisited.Solution

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

@[expose] public section

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
    InhabitedConcreteAt m concrete w :=
  TruthCore.Results.Causality.Round4Revisited.inhabitedFromProduction m concrete w Occurs
    Bears a hO hB hEx hProd hE hFloor.2

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
    InhabitedConcreteAt m concrete w :=
  TruthCore.Results.Causality.Round4Revisited.inhabitedFromPower m concrete w Occurs Bears
    a hasCausalPower hO hB hEx hPow hE hFloor.1

/-! ## From rival refutations to the denied principle -/

/-- No thing is in act without being (the Meinongian rival fails), hence, by
excluded middle on `InAct x esse`, whatever is in act in some respect is in act
as to being. -/
theorem actualityOnlyInsofarAsBeingFromRefutation {B R : Type} (InAct : B → R → Prop)
    (esse : R) (hEM : ExcludedMiddle) (hNo : NoActualityWithoutBeing InAct esse) :
    ActualityOnlyInsofarAsBeingReading InAct esse := by
  intro x r hx
  rcases hEM (InAct x esse) with h | h
  · exact h
  · exact absurd ⟨x, r, hx, h⟩ hNo

/-- The Scotist rival fails: nothing is in act and in potency in one respect,
which is the Prima Via principle read constructively (`¬ ∃` to `∀ ¬`). -/
theorem notActAndPotencyFromRefutation {B R : Type} (InAct InPotency : B → R → Prop)
    (hNo : NoActAndPotencyInSameRespect InAct InPotency) :
    NotActAndPotencyInSameRespectReading InAct InPotency :=
  fun x r ⟨hAct, hPot⟩ => hNo ⟨x, r, hAct, hPot⟩

/-- The Ash'arite rival fails, hence, by excluded middle on `InPotency x r`,
whatever is moved in a respect is in potency in it. -/
theorem movedOnlyAsInPotencyFromAshariteRefutation {B R : Type}
    (MovedIn InPotency : B → R → Prop) (hEM : ExcludedMiddle)
    (hNo : NoMovedWithoutPotency MovedIn InPotency) :
    MovedOnlyAsInPotencyReading MovedIn InPotency := by
  intro x r hx
  rcases hEM (InPotency x r) with h | h
  · exact h
  · exact absurd ⟨x, r, hx, h⟩ hNo

/-- The exact moved-not-potent countertuple fails, hence, by excluded middle,
whatever is moved in a respect is in potency in it. -/
theorem movedOnlyAsInPotencyFromCountertupleRefutation {B R : Type}
    (MovedIn InPotency : B → R → Prop) (hEM : ExcludedMiddle)
    (hNo : NoMovedNotPotentCountertuple MovedIn InPotency) :
    MovedOnlyAsInPotencyReading MovedIn InPotency := by
  intro x r hx
  rcases hEM (InPotency x r) with h | h
  · exact h
  · exact absurd ⟨x, r, hx, h⟩ hNo

/-- The occasionalist rival fails, hence, by excluded middle on
`CausesAsCaused y x`, every per se mover link is a per se cause link. -/
theorem perSeMoverLinkFromOccasionalistRefutation {B : Type}
    (MovesAsMoved CausesAsCaused : B → B → Prop) (hEM : ExcludedMiddle)
    (hNo : NoMoverLinkWithoutCauseLink MovesAsMoved CausesAsCaused) :
    PerSeMoverLinkIsPerSeCauseLinkReading MovesAsMoved CausesAsCaused := by
  intro y x hyx
  rcases hEM (CausesAsCaused y x) with h | h
  · exact h
  · exact absurd ⟨y, x, hyx, h⟩ hNo

/-- Some doubt whether thought occurs is performed; by the retorsion its content
'no thought episode occurs' is then false; by excluded middle some thought
episode occurs. -/
theorem thoughtOccursFromRetorsion {Act Episode : Type}
    (Performed DoubtsThought : Act → Prop) (Occurs : Episode → Prop)
    (hEM : ExcludedMiddle)
    (hDoubt : DoubtIsPerformed Performed DoubtsThought)
    (hSelf : PerformedDoubtOfThoughtSelfRefuting Performed DoubtsThought Occurs) :
    ThoughtOccurs Occurs := by
  obtain ⟨a, hPerf, hDoubts⟩ := hDoubt
  rcases hEM (∃ e, Occurs e) with h | h
  · exact h
  · exact absurd h (hSelf a hPerf hDoubts)

/-! ## Controls -/

section Controls
open TruthCore.Causality.RootWiring.Control
open TruthCore.Causality.Round2ExistenceAct.Control (ont att)

theorem omitFloorActivity_holds : omitFloorActivity := by
  refine ⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial,
    fun _ _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial, ?_, ?_⟩
  · intro h
    exact h.2 () () trivial
  · rintro ⟨_, h, _⟩
    exact h

theorem omitFloorPower_holds : omitFloorPower := by
  refine ⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial,
    fun _ _ _ => trivial, fun _ _ _ _ => trivial, ?_, ?_⟩
  · intro h
    exact h.1 () trivial
  · rintro ⟨_, h, _⟩
    exact h

theorem omitMeinong_holds : omitMeinong := by
  refine ⟨fun h => h ⟨(), false, rfl, fun h' => Bool.noConfusion h'⟩, fun h => ?_⟩
  exact Bool.noConfusion (h () false rfl)

theorem omitScotist_holds : omitScotist :=
  ⟨fun h => h ⟨(), (), trivial, trivial⟩, fun h => h () () ⟨trivial, trivial⟩⟩

theorem omitAsharite_holds : omitAsharite :=
  ⟨fun h => h ⟨(), (), trivial, id⟩, fun h => h () () trivial⟩

theorem omitCountertuple_holds : omitCountertuple :=
  ⟨fun h => h ⟨(), (), trivial, id⟩, fun h => h () () trivial⟩

theorem omitOccasionalist_holds : omitOccasionalist :=
  ⟨fun h => h ⟨(), (), trivial, id⟩, fun h => h () () trivial⟩

theorem omitRetorsion_holds : omitRetorsion := by
  refine ⟨⟨(), trivial, trivial⟩, fun h => h () trivial trivial ?_, ?_⟩
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨_, h⟩
    exact h

theorem omitDoubtPerformed_holds : omitDoubtPerformed := by
  refine ⟨?_, fun _ h => h.elim, ?_⟩
  · rintro ⟨_, h, _⟩
    exact h
  · rintro ⟨_, h⟩
    exact h

theorem witness_holds : witness :=
  ⟨⟨(), trivial⟩, fun _ _ => ⟨(), trivial⟩, fun _ _ _ _ => trivial,
    fun _ _ _ => ⟨(), trivial⟩, fun _ _ _ => trivial, fun _ _ _ _ => trivial,
    ⟨fun _ _ => trivial, fun _ _ _ => trivial⟩, ⟨(), trivial, trivial⟩,
    fun ⟨_, _, _, h⟩ => h trivial, fun _ _ _ => trivial,
    fun ⟨_, _, _, h⟩ => h, fun _ _ ⟨_, h⟩ => h,
    fun ⟨_, _, _, h⟩ => h trivial, fun ⟨_, _, _, h⟩ => h trivial, fun _ _ _ => trivial,
    fun ⟨_, _, _, h⟩ => h trivial, fun _ _ _ => trivial,
    ⟨(), trivial, trivial⟩, fun _ _ _ h => h ⟨(), trivial⟩, ⟨(), trivial⟩⟩

/-- The batch controls: one omission model for the carrying premise of each
derivation and one joint nonvacuity witness. -/
theorem controls : Certificate :=
  ⟨omitFloorActivity_holds, omitFloorPower_holds, omitMeinong_holds, omitScotist_holds,
    omitAsharite_holds, omitCountertuple_holds, omitOccasionalist_holds, omitRetorsion_holds,
    omitDoubtPerformed_holds, witness_holds⟩

end Controls

end TruthCore.Results.Causality.RootWiring
