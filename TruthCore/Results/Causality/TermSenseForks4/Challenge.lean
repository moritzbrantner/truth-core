import TruthCore.Causality.TermSenseForks4
import TruthCore.Results.Case.Catholicism.Skeleton.Solution
import TruthCore.Greek.Aristotle.Metaphysics
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
import TruthCore.Logic.ExcludedMiddle

/-! Sense forks, batch 4: per-sense theorems for "mutable" and "God", the
strength-order theorems, the optional joint summaries and the controls.
Analyst formulations, attribution deferred. -/

namespace TruthCore.Results.Causality.TermSenseForks4

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Causality.TermSenseForks

/-! ## "mutable": one theorem per sense -/

/-- MUTABLE_2 (THROUGH_ANOTHER): whatever begins or ceases to live is in
another's power, and (sense bridge) whatever is in another's power is in
potency in itself; so whatever begins or ceases to live is in potency in
itself. -/
theorem lifeBoundaryPotencyThroughAnother {Being Respect Time : Type} [LT Time]
    (InPotency : Being → Respect → Prop) (PowerOver : Being → Being → Respect → Prop)
    (LivesAt : Being → Time → Prop)
    (hAnother : LifeBoundaryRequiresPowerInAnother PowerOver LivesAt)
    (hBridge : SubjectOfAnothersPowerHasPotency InPotency PowerOver) :
    LifeBoundaryRequiresPotencyReading InPotency LivesAt := by
  sorry

/-- MUTABLE_3 (IN_SOME_WAY): whatever begins or ceases to live is mutable in
itself or through another, and (sense bridge) whatever is in another's power is
in potency in itself; so whatever begins or ceases to live is in potency in
itself. Proof by cases over the two channels. -/
theorem lifeBoundaryPotencyFromSomeMutability {Being Respect Time : Type} [LT Time]
    (InPotency : Being → Respect → Prop) (PowerOver : Being → Being → Respect → Prop)
    (LivesAt : Being → Time → Prop)
    (hSome : LifeBoundaryRequiresSomeMutability InPotency PowerOver LivesAt)
    (hBridge : SubjectOfAnothersPowerHasPotency InPotency PowerOver) :
    LifeBoundaryRequiresPotencyReading InPotency LivesAt := by
  sorry

/-- Strength order MUTABLE_1 → MUTABLE_3 in the boundary use. -/
theorem lifeBoundarySomeMutabilityFromSubject {Being Respect Time : Type} [LT Time]
    (InPotency : Being → Respect → Prop) (PowerOver : Being → Being → Respect → Prop)
    (LivesAt : Being → Time → Prop)
    (hSubject : LifeBoundaryRequiresPotencyReading InPotency LivesAt) :
    LifeBoundaryRequiresSomeMutability InPotency PowerOver LivesAt := by
  sorry

/-- Strength order MUTABLE_2 → MUTABLE_3 in the boundary use. -/
theorem lifeBoundarySomeMutabilityFromAnother {Being Respect Time : Type} [LT Time]
    (InPotency : Being → Respect → Prop) (PowerOver : Being → Being → Respect → Prop)
    (LivesAt : Being → Time → Prop)
    (hAnother : LifeBoundaryRequiresPowerInAnother PowerOver LivesAt) :
    LifeBoundaryRequiresSomeMutability InPotency PowerOver LivesAt := by
  sorry

/-- Optional summary over MUTABLE_1-3: with both uses of "in potency in some
respect" (succession, boundary) covered and one sense selected, whatever is
immutable in that sense has a life without beginning, end or succession. -/
theorem unchangingLifeByMutabilitySenseFork {Being Respect Time State : Type} [LT Time]
    (InPotency : Being → Respect → Prop) (PowerOver : Being → Being → Respect → Prop)
    (LivesAt : Being → Time → Prop) (lifeStateAt : Being → Time → State)
    (Select : MutabilitySense → Prop) (use : MutabilityUse → Being → Prop)
    (hCover : MutabilitySensesExhaustive InPotency PowerOver Select use)
    (hUnique : MutabilitySenseUnique Select)
    (hSuccession : RouteSuccessionIsMutability LivesAt lifeStateAt use)
    (hBoundary : RouteBoundaryIsMutability LivesAt use) :
    RouteImmutableHasUnchangingLife LivesAt lifeStateAt use := by
  sorry

/-! ## "God": one theorem per sense -/

/-- GOD_1 (NOMINAL): read nominally, the naming premise is analytic: whatever
meets the full description is God in what the name signifies. -/
theorem nominalGodNamesDescribedPrinciple {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) :
    NominalGodNamesDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf := by
  sorry

/-- GOD_1 (NOMINAL): read nominally, the converse is analytic too: whatever is
God in what the name signifies is maximal in being. -/
theorem nominalGodIsMaximalInBeing {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) :
    NominalGodIsMaximalInBeing InAct MoreIn CausesIn esse ComponentOf := by
  sorry

/-- GOD_1 → root premise: the sense bridge (whatever meets the full nominal
description is the God of classical theism) gives the CLASSICAL naming premise.
A transcription: the bridge's consequent is the conclusion's. -/
theorem godNamesDescribedFromNominal (σ : Signature) {Respect : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (hBridge : NominalGodIsClassicalGod σ InAct MoreIn CausesIn esse ComponentOf) :
    GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod := by
  sorry

/-- Converse: the CLASSICAL naming premise gives the NOMINAL → CLASSICAL
bridge. With `godNamesDescribedFromNominal`, the root premise is equivalent to
the bridge. -/
theorem nominalBridgeFromGodNames (σ : Signature) {Respect : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (hNames : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod) :
    NominalGodIsClassicalGod σ InAct MoreIn CausesIn esse ComponentOf := by
  sorry

/-- GOD_2 (SUMMA): the reduced naming premise for the Summa's `God` and the
bridge from it to the God of classical theism give the CLASSICAL naming
premise; the fuller description's extra conditions are dropped. -/
theorem godNamesDescribedFromSumma (σ : Signature) {Respect : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf : σ.Being → σ.Being → Prop) (God : σ.Being → Prop)
    (hSumma : GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God)
    (hBridge : SummaGodIsClassicalGod σ God) :
    GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod := by
  sorry

/-- GOD_3 (USAGE): whatever meets the full description is called God, and
whatever is called God is the God of classical theism; so the CLASSICAL naming
premise. -/
theorem godNamesDescribedFromUsage (σ : Signature) {Respect Name : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf : σ.Being → σ.Being → Prop) (Calls : Name → σ.Being → Prop) (godName : Name)
    (hUsage : DescribedPrincipleIsCalledGod InAct MoreIn CausesIn esse ComponentOf Calls godName)
    (hBridge : CalledGodIsClassicalGod σ Calls godName) :
    GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod := by
  sorry

/-- Optional summary over GOD_1-4: with both uses of "God" (naming,
attributes) covered and one sense selected, the fully described principle has
the classical attributes. -/
theorem describedPrincipleAttributesByGodSenseFork (σ : Signature) {Respect Name : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf : σ.Being → σ.Being → Prop) (God : σ.Being → Prop)
    (Calls : Name → σ.Being → Prop) (godName : Name)
    (Select : GodSense → Prop) (use : GodUse → σ.Being → Prop)
    (hCover : GodSensesExhaustive σ InAct MoreIn CausesIn esse ComponentOf God Calls godName
      Select use)
    (hUnique : GodSenseUnique Select)
    (hNaming : RouteNamesDescribedPrinciple σ InAct MoreIn CausesIn esse ComponentOf use)
    (hAttributes : RouteGodHasClassicalAttributes σ use) :
    DescribedPrincipleHasClassicalAttributes σ InAct MoreIn CausesIn esse ComponentOf := by
  sorry

/-! ## The quarta via's own conclusion on the root route (#1237 connection plan) -/

/-- Stage 1 from the quarta via's own conclusion: some MAXIMAL being causes
being in every other being (STMT-MAXIME-ENS-CAUSES-BEING-OF-ALL). That witness
is the only maximal being (a second one would have being caused by the first,
so be exceeded by it), causes every perfection of every other being, and is
remote from all; so, by the fuller naming premise, God exists. The quarta via's
grades, approach, truth-to-being and genus premises are replaced by its
conclusion. -/
theorem godExistsFromMaximeEnsCausingAll {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf PriorSimply : Being → Being → Prop) (IsGod : Being → Prop)
    (hMaxime : MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
      CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf IsGod) :
    GodExists IsGod := by
  sorry

/-- Catholicism (phase 1) from the quarta via's own conclusion: the root route
CATHOLICISM-FROM-FULL-DESCRIPTION-WITHOUT-MOTION with its four quarta via
premises (grades found in things, grades by approach to a maximum, most true is
most being, the maximum in a genus causes all in it) replaced by their
conclusion STMT-MAXIME-ENS-CAUSES-BEING-OF-ALL. -/
theorem catholicismFromMaximeEnsCausingAll (σ : Signature) {Respect : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf PriorSimply : σ.Being → σ.Being → Prop)
    (hMaxime : MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading InAct esse)
    (hCauseMore : TruthCore.Greek.Aristotle.Metaphysics.CauseOfQualityInAnotherIsMoreSuchReading
      CausesIn MoreIn)
    (hEM : TruthCore.Logic.ExcludedMiddle)
    (hPerfections : CauseOfBeingCausesEveryPerfection InAct CausesIn esse)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hFirstBeing : MaximumInBeingIsFirstBeing InAct MoreIn esse PriorSimply)
    (hFull : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod)
    (hAttributes : GodHasClassicalAttributes σ)
    (hRevelation : RevelationPossibleAndRecognizable σ)
    (hJesus : JesusClaimedDivineAuthorityAndRose σ)
    (hFounded : ChristFoundedVisibleChurch σ)
    (hCatholic : ChristsChurchIsCatholicChurch σ)
    (hDivineFounding : BridgeChristsChurchFoundedByGod σ)
    (hOnlyTruth : BridgeGodFoundedAuthorityProposesOnlyTruth σ)
    (hProposes : CatholicChurchDefinitivelyProposesCreed σ) :
    CatholicismTrue σ := by
  sorry

/-! ## Controls -/

theorem termSenseForks4Controls : TermSenseForks4Controls := by
  sorry

end TruthCore.Results.Causality.TermSenseForks4
