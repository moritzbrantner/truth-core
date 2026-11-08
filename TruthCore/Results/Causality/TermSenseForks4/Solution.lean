module

public import TruthCore.Causality.TermSenseForks4
public import TruthCore.Results.Case.Catholicism.Skeleton.Solution
public import TruthCore.Greek.Aristotle.Metaphysics
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article8
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question4.Article1
public import TruthCore.Logic.ExcludedMiddle

/-! Sense forks, batch 4: per-sense theorems for "mutable" and "God", the
strength-order theorems, the optional joint summaries and the controls.
Analyst formulations, attribution deferred. -/

@[expose] public section

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
  intro x hx
  exact hBridge x (hAnother x hx)

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
  intro x hx
  rcases hSome x hx with hSubject | hAnother
  · exact hSubject
  · exact hBridge x hAnother

/-- Strength order MUTABLE_1 → MUTABLE_3 in the boundary use. -/
theorem lifeBoundarySomeMutabilityFromSubject {Being Respect Time : Type} [LT Time]
    (InPotency : Being → Respect → Prop) (PowerOver : Being → Being → Respect → Prop)
    (LivesAt : Being → Time → Prop)
    (hSubject : LifeBoundaryRequiresPotencyReading InPotency LivesAt) :
    LifeBoundaryRequiresSomeMutability InPotency PowerOver LivesAt := by
  intro x hx
  exact Or.inl (hSubject x hx)

/-- Strength order MUTABLE_2 → MUTABLE_3 in the boundary use. -/
theorem lifeBoundarySomeMutabilityFromAnother {Being Respect Time : Type} [LT Time]
    (InPotency : Being → Respect → Prop) (PowerOver : Being → Being → Respect → Prop)
    (LivesAt : Being → Time → Prop)
    (hAnother : LifeBoundaryRequiresPowerInAnother PowerOver LivesAt) :
    LifeBoundaryRequiresSomeMutability InPotency PowerOver LivesAt := by
  intro x hx
  exact Or.inr (hAnother x hx)

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
  have hAgree := usesAgree_of_cover_unique _ Select use hCover hUnique
  intro x hx
  refine ⟨fun hb => hx ?_, fun hs => hx (hSuccession x hs)⟩
  rw [hAgree .succession .boundary]
  exact hBoundary x hb

/-! ## "God": one theorem per sense -/

/-- GOD_1 (NOMINAL): read nominally, the naming premise is analytic: whatever
meets the full description is God in what the name signifies. -/
theorem nominalGodNamesDescribedPrinciple {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) :
    NominalGodNamesDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf := by
  intro m h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-- GOD_1 (NOMINAL): read nominally, the converse is analytic too: whatever is
God in what the name signifies is maximal in being. -/
theorem nominalGodIsMaximalInBeing {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) :
    NominalGodIsMaximalInBeing InAct MoreIn CausesIn esse ComponentOf := by
  intro g hg
  exact hg.1

/-- GOD_1 → root premise: the sense bridge (whatever meets the full nominal
description is the God of classical theism) gives the CLASSICAL naming premise.
A transcription: the bridge's consequent is the conclusion's. -/
theorem godNamesDescribedFromNominal (σ : Signature) {Respect : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (hBridge : NominalGodIsClassicalGod σ InAct MoreIn CausesIn esse ComponentOf) :
    GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod := by
  intro m h1 h2 h3 h4 h5
  exact hBridge m ⟨h1, h2, h3, h4, h5⟩

/-- Converse: the CLASSICAL naming premise gives the NOMINAL → CLASSICAL
bridge. With `godNamesDescribedFromNominal`, the root premise is equivalent to
the bridge. -/
theorem nominalBridgeFromGodNames (σ : Signature) {Respect : Type}
    (InAct : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (ComponentOf : σ.Being → σ.Being → Prop)
    (hNames : GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf σ.IsGod) :
    NominalGodIsClassicalGod σ InAct MoreIn CausesIn esse ComponentOf := by
  intro m hm
  exact hNames m hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.1 hm.2.2.2.2

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
  intro m h1 h2 _ _ h5
  exact hBridge m (hSumma m h1 h2 h5)

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
  intro m h1 h2 h3 h4 h5
  exact hBridge m (hUsage m h1 h2 h3 h4 h5)

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
  have hAgree := usesAgree_of_cover_unique _ Select use hCover hUnique
  intro m hm
  apply hAttributes m
  rw [hAgree .attributes .naming]
  exact hNaming m hm

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
  obtain ⟨m, hMax, hCauses⟩ := hMaxime
  have hUnique : ∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m := by
    intro m' hMax'
    rcases hEM (m' = m) with h | hne
    · exact h
    · exact absurd (hCauseMore m m' esse (fun h => hne h.symm) (hCauses m' hne hMax'.1))
        (hMax'.2 m)
  have hEvery : CausesEveryPerfectionOfOthers InAct CausesIn m :=
    fun x r hOther hAct => hPerfections m x r (hCauses x hOther (hBeing x r hAct)) hAct
  have hRemote : RemoteFromAll ComponentOf m :=
    fun x hComponent => hNoComponent m x hComponent (hFirstBeing m hMax)
  exact ⟨m, hFull m hMax hCauses hEvery hRemote hUnique⟩

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
    CatholicismTrue σ :=
  TruthCore.Results.Case.Catholicism.Skeleton.catholicismSkeleton σ
    (godExistsFromMaximeEnsCausingAll InAct MoreIn CausesIn esse ComponentOf PriorSimply σ.IsGod
      hMaxime hBeing hCauseMore hEM hPerfections hNoComponent hFirstBeing hFull)
    hAttributes hRevelation hJesus hFounded hCatholic hDivineFounding hOnlyTruth hProposes

/-! ## Controls -/

/-- A one-point signature with the given God and attribute predicates; the
historical and creedal fields are unused placeholders. -/
def pointSignature (isGod attrs : Prop) : Signature where
  Being := Unit
  IsGod := fun _ => isGod
  HasClassicalAttributes := fun _ => attrs
  RevealsRecognizably := fun _ => False
  jesus := ()
  ClaimedDivineAuthority := fun _ => False
  RoseFromTheDead := fun _ => False
  Society := Unit
  catholicChurch := ()
  Founded := fun _ _ => False
  VisibleWithAuthority := fun _ => False
  FoundedAsTeachingAuthority := fun _ _ => False
  DefinitivelyProposesAsRevealed := fun _ _ => False
  creedOneGodFatherAlmightyCreator := False
  creedOneLordJesusChristOnlyBegottenConsubstantial := False
  creedIncarnateOfSpiritAndVirginMary := False
  creedCrucifiedUnderPilateSufferedBuried := False
  creedRoseOnTheThirdDay := False
  creedAscendedSeatedAtRightHand := False
  creedWillComeToJudgeKingdomWithoutEnd := False
  creedHolySpiritLordGiverOfLife := False
  creedOneHolyCatholicApostolicChurch := False
  creedOneBaptismForForgiveness := False
  creedResurrectionOfTheDead := False
  creedLifeOfTheWorldToCome := False

/-- In the one-point model with everything in act, nothing more than anything
and no components, the one being meets the full description. -/
private theorem pointNominal (isGod attrs : Prop) :
    NominalGod (Being := (pointSignature isGod attrs).Being) (Respect := Unit)
      (fun _ _ => True) (fun _ _ _ => False) (fun _ _ _ => True) () (fun _ _ => False) () :=
  ⟨⟨trivial, fun _ h => h⟩, fun _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ h => h,
    fun _ _ => rfl⟩

/-- `false` begins to live: absent at 0, present at 1. -/
private theorem falseBegins (LivesAt : Bool → Nat → Prop)
    (h0 : ¬ LivesAt false 0) (h1 : LivesAt false 1) : LifeBeginsOrEnds LivesAt false :=
  ⟨0, 1, by decide, fun h => h0 (h.mpr h1)⟩

/-- The mixed reading of "mutable": succession IN_SUBJECT, boundary
THROUGH_ANOTHER. -/
def mixedMutabilityUse : MutabilityUse → Bool → Prop
  | .succession => MutableInSubject (fun x (_ : Unit) => x = true)
  | .boundary => MutableThroughAnother (fun y x (_ : Unit) => y = true ∧ x = false)

/-- The mixed reading of "God": naming NOMINAL, attributes CLASSICAL. -/
def mixedGodUse : GodUse → (pointSignature False False).Being → Prop
  | .naming => NominalGod (Respect := Unit) (fun _ _ => True) (fun _ _ _ => False)
      (fun _ _ _ => True) () (fun _ _ => False)
  | .attributes => (pointSignature False False).IsGod

theorem termSenseForks4Controls : TermSenseForks4Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- mutable, mixed reading
    refine ⟨fun x _ => x = true, fun y x _ => y = true ∧ x = false,
      fun x t => x = true ∨ t = 1, fun _ _ => (),
      fun s => s = .inSubject ∨ s = .throughAnother,
      mixedMutabilityUse, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      cases u
      · exact ⟨.inSubject, Or.inl rfl, rfl⟩
      · exact ⟨.throughAnother, Or.inr rfl, rfl⟩
    · intro h
      exact absurd (h _ _ (Or.inl rfl) (Or.inr rfl)) (by decide)
    · rintro x ⟨_, _, _, _, _, hne⟩
      exact absurd rfl hne
    · intro x hx
      cases x
      · exact ⟨true, (), by decide, rfl, rfl⟩
      · obtain ⟨_, _, _, h⟩ := hx
        exact absurd (Iff.intro (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)) h
    · intro h
      have hfalse : ¬ MutableInSubject (fun (x : Bool) (_ : Unit) => x = true) false := by
        rintro ⟨_, h⟩
        exact absurd h (by decide)
      exact (h false hfalse).1
        (falseBegins _ (by rintro (h | h) <;> exact absurd h (by decide)) (Or.inr rfl))
  · -- mutable, nonvacuity
    refine ⟨fun _ _ => False, fun _ _ _ => False, fun _ _ => True, fun _ _ => (),
      fun s => s = .inSubject, fun _ => MutableInSubject (fun (_ : Bool) (_ : Unit) => False), ?_, ?_, ?_, ?_, ?_,
      ⟨true, 0, trivial⟩⟩
    · intro u
      exact ⟨.inSubject, rfl, rfl⟩
    · intro σ τ hσ hτ
      rw [hσ, hτ]
    · rintro x ⟨_, _, _, _, _, hne⟩
      exact absurd rfl hne
    · rintro x ⟨_, _, _, h⟩
      exact absurd (Iff.intro (fun _ => trivial) (fun _ => trivial)) h
    · intro x _
      refine ⟨?_, ?_⟩
      · rintro ⟨_, _, _, h⟩
        exact h (Iff.intro (fun _ => trivial) (fun _ => trivial))
      · rintro ⟨_, _, _, _, _, hne⟩
        exact hne rfl
  · -- mutable, bridge omitted
    refine ⟨fun _ _ => False, fun y x _ => y ≠ x, fun x t => x = true ∨ t = 1, ?_, ?_, ?_⟩
    · intro x _
      exact ⟨!x, (), by cases x <;> decide, by cases x <;> decide⟩
    · intro x _
      exact Or.inr ⟨!x, (), by cases x <;> decide, by cases x <;> decide⟩
    · intro h
      obtain ⟨_, hr⟩ := h false
        (falseBegins _ (by rintro (h | h) <;> exact absurd h (by decide)) (Or.inr rfl))
      exact hr
  · -- mutable, boundary premise omitted
    refine ⟨fun _ _ => False, fun _ _ _ => False, fun _ t => t = 1, ?_, ?_⟩
    · rintro x ⟨_, _, _, h⟩
      exact h.elim
    · intro h
      obtain ⟨_, hr⟩ := h () ⟨0, 1, by decide, fun h' => absurd (h'.mpr rfl) (by decide)⟩
      exact hr
  · -- God, mixed reading
    refine ⟨pointSignature False False, fun _ _ => True, fun _ _ _ => False,
      fun _ _ _ => True, fun _ _ => False, fun _ => False, fun _ _ => False,
      fun s => s = .nominal ∨ s = .classical,
      mixedGodUse, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      cases u
      · exact ⟨.nominal, Or.inl rfl, rfl⟩
      · exact ⟨.classical, Or.inr rfl, rfl⟩
    · intro h
      exact absurd (h _ _ (Or.inl rfl) (Or.inr rfl)) (by decide)
    · intro m hm
      exact hm
    · intro g hg
      exact hg
    · intro h
      exact h () (pointNominal False False)
  · -- God, nonvacuity
    refine ⟨pointSignature True True, fun _ _ => True, fun _ _ _ => False,
      fun _ _ _ => True, fun _ _ => False, fun _ => True, fun _ _ => True,
      fun s => s = .classical, fun _ => (pointSignature True True).IsGod, ?_, ?_, ?_, ?_, ?_,
      ⟨(), pointNominal True True⟩⟩
    · intro u
      exact ⟨.classical, rfl, rfl⟩
    · intro σ τ hσ hτ
      rw [hσ, hτ]
    · intro _ _
      exact trivial
    · intro _ _
      exact trivial
    · intro _ _
      exact trivial
  · -- God, branches without their bridges
    refine ⟨pointSignature False False, fun _ _ => True, fun _ _ _ => False,
      fun _ _ _ => True, fun _ _ => False, fun _ => True, fun _ _ => True, ?_, ?_, ?_,
      ⟨(), pointNominal False False⟩, ?_⟩
    · exact nominalGodNamesDescribedPrinciple _ _ _ _ _
    · intro _ _ _ _
      exact trivial
    · intro _ _ _ _ _ _
      exact trivial
    · intro h
      obtain ⟨h1, h2, h3, h4, h5⟩ := pointNominal False False
      exact h () h1 h2 h3 h4 h5
  · -- God, usage naming omitted
    refine ⟨pointSignature False False, fun _ _ => True, fun _ _ _ => False,
      fun _ _ _ => True, fun _ _ => False, fun _ _ => False, ?_, ?_⟩
    · intro _ h
      exact h.elim
    · intro h
      obtain ⟨h1, h2, h3, h4, h5⟩ := pointNominal False False
      exact h () h1 h2 h3 h4 h5
  · -- stage 1 from the quarta via's conclusion, that conclusion omitted
    refine ⟨fun _ _ => False, fun _ _ _ => False, fun _ _ _ => False, fun _ _ => False,
      fun _ _ => False, fun _ => False, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨_, ⟨h, _⟩, _⟩
      exact h
    · intro _ _ h
      exact h.elim
    · intro _ _ _ hne
      exact absurd rfl hne
    · intro _ _ _ h
      exact h.elim
    · intro _ _ h
      exact h.elim
    · intro _ h
      exact h.1.elim
    · intro _ h
      exact h.1.elim
    · rintro ⟨_, h⟩
      exact h

end TruthCore.Results.Causality.TermSenseForks4
