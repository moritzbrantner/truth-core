module

public import TruthCore.Causality.NamingVeracityBatch1

/-! Batch 1 of the naming, veracity, revelation and authority maps; every theorem is conditional on its OPEN hypotheses. -/

@[expose] public section

namespace TruthCore.Results.Causality.NamingVeracityBatch1
open TruthCore.Causality.NamingVeracityBatch1
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Latin.Aquinas.SummaTheologiae (IsMaximumIn CausesAllInGenus)

/-! ## Naming -/

/-- Strength registration: the reduced naming leaf entails the fuller one,
since the fuller description only adds antecedents. -/
theorem reducedNamingEntailsFull {B R : Type} (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (ComponentOf : B → B → Prop) (God : B → Prop)
    (hReduced : GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God) :
    GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf God :=
  fun m hMax hCause _ _ hUniq => hReduced m hMax hCause hUniq

/-- If the name "God" applies to the only universal cause of being, and every
universal cause of being is maximal in being, then it applies to the only
maximum in being that causes all being: a second universal cause would be a
second maximum. -/
theorem reducedNamingFromOperation {B R : Type} (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R) (God : B → Prop)
    (hName : NameGodImposedFromOperation InAct CausesIn esse God)
    (hMax : UniversalCauseOfBeingIsMaximal InAct MoreIn CausesIn esse) :
    GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse God :=
  fun m _ hCause hUniq => hName m hCause fun m' hC' => hUniq m' (hMax m' hC')

/-! ## Veracity -/

/-- Whatever a God with the classical attributes confirms, he asserts; what he
asserts he holds as known; what he holds as known is true. -/
theorem godConfirmsOnlyTruthFromVeracity (σ : Signature) (A : Agency σ) (V : Veracity σ)
    (hAssert : ConfirmingIsAsserting σ A V)
    (hSincere : GodAssertsOnlyWhatHeKnows σ V)
    (hInfallible : GodKnowsOnlyTruths σ V) :
    GodConfirmsOnlyTruth σ A :=
  fun g hg hAttr p hConf => hInfallible g hg hAttr p (hSincere g hg hAttr p (hAssert g p hConf))

/-- Sincerity from the attributes: a good will asserts only what it believes,
and a perfect intellect believes only what it knows. -/
theorem godAssertsOnlyWhatHeKnowsFromAttributes (σ : Signature) (V : Veracity σ)
    (hAttrs : ClassicalAttributesIncludePerfectIntellectAndGoodWill σ V) :
    GodAssertsOnlyWhatHeKnows σ V :=
  fun g hg hAttr p hAsserts =>
    (hAttrs g hg hAttr).2 p ((hAttrs g hg hAttr).1 p hAsserts)

/-! ## Authority -/

/-- A God who founds a teaching authority assists it, and what an assisted
society definitively proposes the assisting God confirms. -/
theorem definitiveProposalConfirmedFromAssistance (σ : Signature) (A : Agency σ)
    (S : Assistance σ)
    (hFounder : FounderGuaranteesFoundedAuthority σ S)
    (hAssisted : AssistedDefinitiveProposalIsConfirmed σ A S) :
    DefinitiveProposalIsGodConfirmed σ A :=
  fun g c hg hAttr hFounded p hProp => hAssisted g c (hFounder g c hg hAttr hFounded) p hProp

/-- Veracity applied to definitive proposals: what a God-founded teaching
authority definitively proposes, its God confirms, and what he confirms is
true. -/
theorem authorityProposesOnlyTruth (σ : Signature) (A : Agency σ)
    (hConfirmed : DefinitiveProposalIsGodConfirmed σ A)
    (hVeracity : GodConfirmsOnlyTruth σ A) :
    BridgeGodFoundedAuthorityProposesOnlyTruth σ :=
  fun g c hg hAttr hFounded p hProp =>
    hVeracity g hg hAttr p (hConfirmed g c hg hAttr hFounded p hProp)

/-! ## Revelation -/

/-- Infinite power from unlimited act: a consistent task requires only possible
perfections, the infinite is in act in each of them, and power follows act. -/
theorem infinitePowerFromAct (σ : Signature) (Infinite : σ.Being → Prop) (P : Power σ)
    (hUnlimited : InfiniteIsUnlimitedAct σ Infinite P)
    (hPower : ActivePowerFollowsAct σ P)
    (hPossible : ConsistentTaskRequiresOnlyPossiblePerfections σ P) :
    InfiniteActHasInfinitePower σ Infinite P :=
  fun x hx t hCons => hPower x t fun r hReq => hUnlimited x hx r (hPossible t hCons r hReq)

/-- God is infinite, and the infinite can do every consistent task. -/
theorem godOmnipotentFromInfinite (σ : Signature) (Infinite : σ.Being → Prop) (P : Power σ)
    (hInfinite : GodIsInfinite σ.IsGod Infinite)
    (hPower : InfiniteActHasInfinitePower σ Infinite P) :
    GodIsOmnipotent σ P :=
  fun g hg t hCons => hPower g (hInfinite g hg) t hCons

/-- God can reveal with signs (omnipotence, no contradiction), only God can give
those signs, and so, by the analysis of recognizable revelation, God reveals
recognizably. -/
theorem revelationFromOmnipotence (σ : Signature) (P : Power σ)
    (hOmni : GodIsOmnipotent σ P)
    (hConsistent : RevelationInvolvesNoContradiction σ P)
    (hOnlyGod : SomeSignsOnlyGodCanGive σ P)
    (hAnalysis : RecognizableRevelationAnalysis σ P) :
    RevelationPossibleAndRecognizable σ :=
  fun g hg => hAnalysis g (hOmni g hg P.revealWithSigns hConsistent) hOnlyGod

/-! ## Controls -/

open Control

theorem nUnique : GodNamesTheUniqueMaximeEns nInAct nMore nCauses () nGod := by
  intro m hMax _ _
  cases m
  · exact (hMax.2 true ⟨rfl, rfl⟩).elim
  · rfl

theorem nCausesAll : UniversalCauseOfBeingIsMaximal nInAct nMore nCauses () := by
  intro m hC
  cases m
  · exact absurd (hC true (by decide) trivial) Bool.false_ne_true
  · exact ⟨trivial, fun _ hy => absurd hy.2 (by decide)⟩

theorem jointWitness : JointWitness :=
  ⟨rfl, trivial, trivial,
    fun _ _ h => h,
    fun _ _ _ _ h => h,
    fun _ _ _ _ h => h,
    fun _ _ _ => ⟨fun _ h => h, fun _ h => h⟩,
    fun _ _ _ _ h => h,
    fun _ _ _ _ _ => trivial,
    fun _ _ _ _ h => h,
    fun _ _ _ _ _ _ h => h,
    fun _ _ _ _ _ _ h => h,
    fun _ hx _ _ => hx,
    fun _ _ h => h () trivial,
    fun _ _ _ _ => trivial,
    fun _ hx _ _ => hx,
    fun _ h => h,
    fun _ h _ _ => h,
    trivial,
    fun _ h => h,
    fun _ _ _ => trivial,
    fun _ _ => trivial,
    fun _ _ _ => rfl,
    fun _ _ hU => (hU true fun _ _ _ => rfl).symm,
    nCausesAll,
    nUnique,
    reducedNamingEntailsFull _ _ _ _ _ _ nUnique⟩

theorem veracityOmissions : VeracityOmissions := by
  refine ⟨⟨_, agency True True (fun _ => True) (fun _ => True),
      veracity True True (fun _ => True) (fun _ => False) (fun _ => False) (fun _ => False),
      ?_, ?_, ?_, ?_⟩,
    ⟨_, agency True True (fun _ => True) (fun _ => True),
      veracity True True (fun _ => True) (fun _ => True) (fun _ => False) (fun _ => False),
      ?_, ?_, ?_, ?_⟩,
    ⟨_, agency True True (fun _ => True) (fun _ => True),
      veracity True True (fun _ => True) (fun _ => True) (fun _ => True) (fun _ => True),
      ?_, ?_, ?_, ?_⟩⟩
  · intro h; exact h true True trivial
  · intro _ _ _ _ h; exact h
  · intro _ _ _ _ h; exact h.elim
  · intro h; exact h true rfl trivial False trivial
  · intro _ _ _; trivial
  · intro h; exact h true rfl trivial True trivial
  · intro _ _ _ _ h; exact h.elim
  · intro h; exact h true rfl trivial False trivial
  · intro _ _ _; trivial
  · intro _ _ _ _ _; trivial
  · intro h; exact h true rfl trivial False trivial
  · intro h; exact h true rfl trivial False trivial

theorem authorityOmissions : AuthorityOmissions := by
  refine ⟨⟨sig True True (fun _ => True), agency True True (fun _ => True) (fun _ => False),
      ?_, ?_, ?_⟩,
    ⟨sig True True (fun _ => True), agency True True (fun _ => True) (fun _ => True),
      ?_, ?_, ?_⟩⟩
  · intro h; exact h true () rfl trivial trivial True trivial
  · intro _ _ _ _ h; exact h.elim
  · intro h; exact h true () rfl trivial trivial False trivial
  · intro _ _ _ _ _ _ _; trivial
  · intro h; exact h true rfl trivial False trivial
  · intro h; exact h true () rfl trivial trivial False trivial

theorem revelationOmissions : RevelationOmissions := by
  refine ⟨⟨sig False True (fun p => p), power False True (fun p => p) True (fun _ => False),
      ?_, ?_, ?_, ?_, ?_⟩,
    ⟨sig False True (fun p => p), power False True (fun p => p) False (fun _ => False),
      ?_, ?_, ?_, ?_, ?_⟩,
    ⟨sig False True (fun p => p), power False True (fun p => p) True (fun _ => True),
      ?_, ?_, ?_, ?_, ?_⟩,
    ⟨sig False True (fun p => p), power False True (fun p => p) True (fun x => x = true),
      ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h; exact h true rfl () trivial
  · trivial
  · intro _ h; exact h.elim
  · intro _ h; exact h.elim
  · intro h; exact h true rfl
  · intro _ _ _ h; exact h.elim
  · intro h; exact h
  · intro _ h; exact h.elim
  · intro _ h; exact h.elim
  · intro h; exact h true rfl
  · intro _ _ _ _; trivial
  · trivial
  · intro h; exact Bool.noConfusion (h false trivial)
  · intro _ _ hOnly; exact Bool.noConfusion (hOnly false trivial)
  · intro h; exact h true rfl
  · intro g hg _ _; exact hg
  · trivial
  · intro _ h; exact h
  · intro h; exact h true rfl (fun _ h => h)
  · intro h; exact h true rfl

theorem namingOmissions : NamingOmissions := by
  refine ⟨⟨nInAct, nMore, nCauses, fun _ => False, ?_, ?_, ?_⟩,
    ⟨nInAct, nMore, fun _ _ _ => True, fun _ => False, ?_, ?_, ?_⟩⟩
  · intro h
    exact h true (fun _ _ _ => rfl) fun m' hC' => by
      cases m'
      · exact absurd (hC' true (by decide) trivial) Bool.false_ne_true
      · rfl
  · exact nCausesAll
  · intro h
    exact h true ⟨trivial, fun _ hy => absurd hy.2 (by decide)⟩ (fun _ _ _ => rfl) fun m' hM => by
      cases m'
      · exact (hM.2 true ⟨rfl, rfl⟩).elim
      · rfl
  · intro m _ hU
    cases m
    · exact absurd (hU true fun _ _ _ => trivial) (by decide)
    · exact absurd (hU false fun _ _ _ => trivial) (by decide)
  · intro h; exact (h false fun _ _ _ => trivial).2 true ⟨rfl, rfl⟩
  · intro h
    exact h true ⟨trivial, fun _ hy => absurd hy.2 (by decide)⟩ (fun _ _ _ => trivial) fun m' hM => by
      cases m'
      · exact (hM.2 true ⟨rfl, rfl⟩).elim
      · rfl

/-- Controls: a joint witness of the whole batch and omission models for each
premise of the four target-reaching steps. -/
theorem controls : Certificate :=
  ⟨jointWitness, veracityOmissions, authorityOmissions, revelationOmissions, namingOmissions⟩

end TruthCore.Results.Causality.NamingVeracityBatch1
