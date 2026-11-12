module

public import TruthCore.Causality.DeiFiliusAttributeField
public import TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Registration.Solution

/-! The stage-two sufficiency premise restated against the defined Dei Filius
attributes (`DeiFiliusAttributeField`). Analyst formulations, attribution
deferred. No premise is established; each theorem is a conditional
consequence of its listed hypotheses. -/

@[expose] public section

namespace TruthCore.Results.Causality.DeiFiliusAttributeField

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessaryClassicalGodRoot
open TruthCore.Causality.DeiFiliusAttributeField
open TruthCore.Causality.NamingVeracityBatch1 (Power InfiniteActHasInfinitePower)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Logic

/-- The nine stage-two attributes give every Dei Filius attribute, from seven
open bridges and three existing premises. Ten conjuncts are the nine
themselves; `creator` unfolds the goodness conjunct (supreme goodness includes
causing every perfection of everything else, so in particular its being);
`spiritual` uses the matter-form clause of the q.3 a.7 composition premise and
simplicity; `exalted` uses goodness-is-actuality (for act as to being) and the
excess-in-act bridge against universal perfection; `almighty` uses the existing
infinite-power premise; `living`, `lord`, `immense`, `incomprehensible`,
`blessed` and `distinct` use one open bridge each. -/
theorem nineGiveDeiFilius (σ : Signature) {Principle Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (essenceOf esseOf : σ.Being → Principle)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being)
    (hLiving : IntellectualIsLiving HasIntellect D)
    (hLord : CreatorOfAllIsLord InAct CausesIn esse D)
    (hPower : InfiniteActHasInfinitePower σ Infinite P)
    (hImmense : CreatorOfAllIsImmense InAct CausesIn esse D)
    (hIncomprehensible : InfiniteIsIncomprehensible Infinite D)
    (hBlessed : PerfectIntellectualIsMostBlessed InAct HasIntellect D)
    (hNoComponent : CreatorOfAllIsNoComponent InAct CausesIn esse ComponentOf)
    (hExcess : ExcessInBeingIsExcessInAct InAct MoreIn esse)
    (hGoodness : GoodnessIsActualityReading GoodIn InAct)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite essenceOf esseOf) :
    NineSufficeForDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D := by
  intro g ⟨hs, hp, hg, ho, hi, hm, he, hx, hw⟩
  have hCreator : IsCreatorOfAll InAct CausesIn esse g := fun x hx hAct => hg.2 x esse hx hAct
  exact
    { one := ho
      living := hLiving g hx
      creator := hCreator
      lord := hLord g hCreator
      almighty := hPower g hi
      eternal := he
      immense := hImmense g hCreator
      incomprehensible := hIncomprehensible g hi
      intellect := hx
      will := hw
      perfect := hp
      infinite := hi
      simple := hs
      immutable := hm
      spiritual := fun hMF => hs ((hKinds g).1 hMF)
      distinct := hNoComponent g hCreator
      blessed := hBlessed g hp hx
      exalted := ⟨(hGoodness g esse).mp hg.1, fun y hMore =>
        let ⟨r, hy, hn⟩ := hExcess y g hMore
        hn (hp y r hy)⟩
      good := hg }

/-- The old sufficiency premise from the restated one and the field
interpretation: compose the two one-way implications at each being. -/
theorem classicalAttributesSufficeOfDeiFilius (σ : Signature) {Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being)
    (hNine : NineSufficeForDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D)
    (hField : FieldFromDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D) :
    ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill :=
  fun g hs hp hg ho hi hm he hx hw =>
    hField g (hNine g ⟨hs, hp, hg, ho, hi, hm, he, hx, hw⟩)

/-- The old sufficiency premise gives the field interpretation: a being with
every Dei Filius attribute has the nine, so the old premise applies: the old
premise is at least as strong as the field interpretation, strictly by
`Control.Controls`, part 3. A checked lemma, deliberately not registered as a
corpus argument (it would close a support cycle with
`classicalAttributesSufficeOfDeiFilius`). -/
theorem fieldOfSuffice (σ : Signature) {Respect : Type}
    (InAct GoodIn InPotency : σ.Being → Respect → Prop)
    (CausesIn : σ.Being → σ.Being → Respect → Prop) (esse : Respect)
    (MoreIn : Respect → σ.Being → σ.Being → Prop) (ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (P : Power σ) (D : Primitives σ.Being)
    (hSuffice : ClassicalAttributesSuffice σ (IsSimple Composite) (IsPerfect InAct)
      (IsSupremelyGood InAct GoodIn CausesIn esse) (IsTheOneGod σ.IsGod)
      Infinite (IsImmutable InPotency) Eternal HasIntellect HasWill) :
    FieldFromDeiFilius σ InAct GoodIn InPotency CausesIn esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill P D := by
  intro g h
  obtain ⟨hs, hp, hg, ho, hi, hm, he, hx, hw⟩ := nineOfDeiFilius σ h
  exact hSuffice g hs hp hg ho hi hm he hx hw

/-- The spine's root with the defined Dei Filius attributes, from the inputs of
the registered join-to-stage-two composition (result 57213a13) WITHOUT the
sufficiency premise, plus six open bridges. The registered composition is
reused on the signature that agrees with `σ` except that its primitive field is
everywhere true (so its sufficiency premise holds trivially there, and nothing
about the field is used); its root then has every Dei Filius attribute:
`distinct`, `spiritual` and `exalted` come from the root's remoteness,
matter-form exclusion and maximum in being, `creator` from its supreme
goodness, `almighty` from infinity through the existing infinite-power premise,
and the five primitives from one bridge each. -/
theorem deiFiliusRoot {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being)
    (hUnderived : NecessaryConcreteUnderivedAt m w) (hEM : ExcludedMiddle)
    (hGenus : MaximumInBeingCausesAllBeingsReading p.InAct MoreIn p.CausesIn p.esse)
    (hExisting : ExistingInActAt m.ontic p.InAct p.esse w)
    (hEsse : EsseCauseIsActualConcreteGround m w p.CausesIn p.esse)
    (hApproach : GradesToMaximumAtBeing p.InAct MoreIn p.esse)
    (hBeing : ActualityOnlyInsofarAsBeingReading p.InAct p.esse)
    (hPreexist : PerfectionsOfEffectPreexistInCauseReading p.InAct p.CausesIn p.esse)
    (hGoodness : GoodnessIsActualityReading GoodIn p.InAct)
    (hTransfer : UniversalCauseTransfersPerfections p.InAct p.CausesIn p.esse)
    (hUniting : CompositeHasAUnitingCauseReading Composite p.CausesIn p.esse)
    (hKinds : MatterFormAndEsseEssenceAreCompositionsReading MatterForm Composite p.essenceOf p.esseOf)
    (hPrior : SimplyPriorIsActualConcreteGround m w PriorSimply)
    (hNoComponent : NoComponentIsFirstBeingReading ComponentOf PriorSimply)
    (hIntellect : ImmaterialIsIntellectualReading MatterForm HasIntellect ComponentOf)
    (hWill : WillFollowsIntellectReading HasIntellect HasWill)
    (hActPrior : TruthCore.Case.Catholicism.ClassicalAttributesLocalLogic.IndependentPriority
      p.InAct InPotency PriorSimply)
    (hNotBoth : NotActAndPotencyInSameRespectReading p.InAct InPotency)
    (hInfinity : SubsistentBeingIsInfiniteReading p.essenceOf p.esseOf Infinite)
    (hEternity : ImmutableIsEternalReading InPotency Eternal)
    (hNaming : GodNamesTheFullyDescribedPrinciple p.InAct MoreIn p.CausesIn p.esse ComponentOf σ.IsGod)
    (hGodMaximal : GodIsMaximalInBeing σ.IsGod p.InAct MoreIn p.esse)
    (hLiving : IntellectualIsLiving HasIntellect D)
    (hLord : CreatorOfAllIsLord p.InAct p.CausesIn p.esse D)
    (hPower : InfiniteActHasInfinitePower σ Infinite Pw)
    (hImmense : CreatorOfAllIsImmense p.InAct p.CausesIn p.esse D)
    (hIncomprehensible : InfiniteIsIncomprehensible Infinite D)
    (hBlessed : PerfectIntellectualIsMostBlessed p.InAct HasIntellect D) :
    NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D := by
  let σ' : Signature := { σ with HasClassicalAttributes := fun _ => True }
  have hRoot : NecessaryClassicalGodRootAt σ' m w p GoodIn InPotency MoreIn PriorSimply
      ComponentOf Composite MatterForm Infinite Eternal HasIntellect HasWill :=
    TruthCore.Results.Causality.NecessaryClassicalGodRootFromUnderived.Registration.derive
      σ' m w p GoodIn InPotency MoreIn PriorSimply ComponentOf Composite MatterForm
      Infinite Eternal HasIntellect HasWill hUnderived hEM hGenus hExisting hEsse hApproach
      hBeing hPreexist hGoodness hTransfer hUniting hKinds hPrior hNoComponent hIntellect hWill
      hActPrior hNotBoth hInfinity hEternity hNaming hGodMaximal
      (fun _ _ _ _ _ _ _ _ _ _ => trivial)
  obtain ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod, hNine, _⟩ := hRoot
  obtain ⟨hs, hp, hg, ho, hi, hm, he, hx, hw⟩ := hNine
  have hCreator : IsCreatorOfAll p.InAct p.CausesIn p.esse n :=
    fun x hx hAct => hg.2 x p.esse hx hAct
  exact ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod,
    { one := ho
      living := hLiving n hx
      creator := hCreator
      lord := hLord n hCreator
      almighty := hPower n hi
      eternal := he
      immense := hImmense n hCreator
      incomprehensible := hIncomprehensible n hi
      intellect := hx
      will := hw
      perfect := hp
      infinite := hi
      simple := hs
      immutable := hm
      spiritual := hNoMF
      distinct := hRemote
      blessed := hBlessed n hp hx
      exalted := hPerfectRoot.2.2.2.1
      good := hg }⟩

/-- The old endpoint from the defined one and the field interpretation: the
nine are among the Dei Filius attributes, and the field interpretation gives
the primitive field at the same witness. -/
theorem classicalRootOfDeiFiliusRoot {W Principle Respect : Type} (σ : Signature)
    (m : Profile W σ.Being) (w : W)
    (p : PrimaPars.Question3.Article4.Profile σ.Being Principle Respect)
    (GoodIn InPotency : σ.Being → Respect → Prop) (MoreIn : Respect → σ.Being → σ.Being → Prop)
    (PriorSimply ComponentOf : σ.Being → σ.Being → Prop)
    (Composite MatterForm Infinite Eternal HasIntellect HasWill : σ.Being → Prop)
    (Pw : Power σ) (D : Primitives σ.Being)
    (hRoot : NecessaryDeiFiliusGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D)
    (hField : FieldFromDeiFilius σ p.InAct GoodIn InPotency p.CausesIn p.esse MoreIn ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill Pw D) :
    NecessaryClassicalGodRootAt σ m w p GoodIn InPotency MoreIn PriorSimply ComponentOf
      Composite MatterForm Infinite Eternal HasIntellect HasWill := by
  obtain ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod, hDF⟩ := hRoot
  exact ⟨n, hPerfectRoot, hId, hFirst, hNoMF, hRemote, hGod, nineOfDeiFilius σ hDF, hField n hDF⟩

/-- The controls of `Control.Controls`, checked by unfolding the one-being
interpretations. -/
theorem controls : Control.Controls := by
  have hDF : ∀ k : Control.Case, Control.DF k ↔
      (k.l ∧ k.o ∧ k.can ∧ k.i ∧ k.c ∧ k.b ∧ ¬ k.composite ∧ ¬ k.matter ∧ ¬ k.comp ∧ ¬ k.more) := by
    intro k
    constructor
    · intro h
      exact ⟨h.living, h.lord, h.almighty () trivial, h.immense, h.incomprehensible, h.blessed,
        h.simple, h.spiritual, h.distinct (), h.exalted.2 ()⟩
    · rintro ⟨hl, ho, hc, hi, hn, hb, hs, hm, hk, hmo⟩
      exact
        { one := fun _ _ => rfl
          living := hl
          creator := fun _ h _ => absurd rfl h
          lord := ho
          almighty := fun _ _ => hc
          eternal := trivial
          immense := hi
          incomprehensible := hn
          intellect := trivial
          will := trivial
          perfect := fun _ _ h => h
          infinite := trivial
          simple := hs
          immutable := fun _ h => h
          spiritual := hm
          distinct := fun _ h => hk h
          blessed := hb
          exalted := ⟨trivial, fun _ h => hmo h⟩
          good := ⟨trivial, fun _ _ h _ => absurd rfl h⟩ }
  have hNine : ∀ k : Control.Case, ¬ k.composite → Control.Nine k := fun k hs =>
    ⟨hs, fun _ _ h => h, ⟨trivial, fun _ _ h _ => absurd rfl h⟩, fun _ _ => rfl, trivial,
      fun _ h => h, trivial, trivial, trivial⟩
  -- Premises at a one-being interpretation, premise by premise.
  have prem : ∀ (k : Control.Case) (skip : Nat),
      (skip ≠ 0 → k.l) → (skip ≠ 1 → k.o) → (skip ≠ 2 → k.can) → (skip ≠ 3 → k.i) →
      (skip ≠ 4 → k.c) → (skip ≠ 5 → k.b) → (skip ≠ 6 → ¬ k.comp) → (skip ≠ 7 → ¬ k.more) →
      (skip ≠ 8 → k.matter → k.composite) → Control.Premises k skip :=
    fun _ _ h0 h1 h2 h3 h4 h5 h6 h7 h8 =>
      ⟨fun hs _ _ => h0 hs, fun hs _ _ => h1 hs, fun hs _ _ _ _ => h2 hs, fun hs _ _ => h3 hs,
        fun hs _ _ => h4 hs, fun hs _ _ _ => h5 hs, fun hs _ _ _ hc => h6 hs hc,
        fun hs _ _ hm => absurd hm (h7 hs), fun _ _ => Iff.rfl,
        fun hs _ => ⟨h8 hs, fun hne => absurd rfl hne⟩⟩
  have t : ∀ {s : Nat}, s ≠ s → False := fun h => h rfl
  refine ⟨⟨prem _ _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
      (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ h => h) (fun _ h => h)
      (fun _ h => h), hNine _ id,
      (hDF _).2 ⟨trivial, trivial, trivial, trivial, trivial, trivial, id, id, id, id⟩⟩,
    ?_, ?_, ?_⟩
  · intro k hk
    match k, hk with
    | 0, _ => exact ⟨prem _ _ (fun h => (t h).elim) (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ h => h) (fun _ h => h)
        (fun _ h => h), hNine _ id, fun h => ((hDF _).1 h).1⟩
    | 1, _ => exact ⟨prem _ _ (fun _ => trivial) (fun h => (t h).elim) (fun _ => trivial)
        (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ h => h) (fun _ h => h)
        (fun _ h => h), hNine _ id, fun h => ((hDF _).1 h).2.1⟩
    | 2, _ => exact ⟨prem _ _ (fun _ => trivial) (fun _ => trivial) (fun h => (t h).elim)
        (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ h => h) (fun _ h => h)
        (fun _ h => h), hNine _ id, fun h => ((hDF _).1 h).2.2.1⟩
    | 3, _ => exact ⟨prem _ _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
        (fun h => (t h).elim) (fun _ => trivial) (fun _ => trivial) (fun _ h => h) (fun _ h => h)
        (fun _ h => h), hNine _ id, fun h => ((hDF _).1 h).2.2.2.1⟩
    | 4, _ => exact ⟨prem _ _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial) (fun h => (t h).elim) (fun _ => trivial) (fun _ h => h) (fun _ h => h)
        (fun _ h => h), hNine _ id, fun h => ((hDF _).1 h).2.2.2.2.1⟩
    | 5, _ => exact ⟨prem _ _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial) (fun _ => trivial) (fun h => (t h).elim) (fun _ h => h) (fun _ h => h)
        (fun _ h => h), hNine _ id, fun h => ((hDF _).1 h).2.2.2.2.2.1⟩
    | 6, _ => exact ⟨prem _ _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun h => (t h).elim)
        (fun _ h => h) (fun _ h => h), hNine _ id,
        fun h => ((hDF _).1 h).2.2.2.2.2.2.2.2.1 trivial⟩
    | 7, _ => exact ⟨prem _ _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ h => h)
        (fun h => (t h).elim) (fun _ h => h), hNine _ id,
        fun h => ((hDF _).1 h).2.2.2.2.2.2.2.2.2 trivial⟩
    | 8, _ => exact ⟨prem _ _ (fun _ => trivial) (fun _ => trivial) (fun _ => trivial)
        (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ h => h) (fun _ h => h)
        (fun h => (t h).elim), hNine _ id,
        fun h => ((hDF _).1 h).2.2.2.2.2.2.2.1 trivial⟩
    | n + 9, hk => exact absurd hk (Nat.not_lt_of_le (Nat.le_add_left 9 n))
  · intro g h
    exact h.living
  · intro hSuffice
    exact (hSuffice () (fun h => h) (fun _ _ h => h) ⟨trivial, fun _ _ h _ => absurd rfl h⟩
      (fun _ _ => rfl) trivial (fun _ h => h) trivial trivial trivial)

end TruthCore.Results.Causality.DeiFiliusAttributeField
