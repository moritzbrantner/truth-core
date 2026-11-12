module

public import TruthCore.Causality.CreatureSenses

/-! Typed CREATURE senses: the CREATURE_2 → CREATURE_1 bridge derived from the
Fourth-Way consequence, and the caused-esse-is-received bridge of the unified Dei
Filius route derived through it. Analyst formulations, attribution deferred. No
premise is established. -/

@[expose] public section

namespace TruthCore.Results.Causality.CreatureSenses

open TruthCore.Latin.Aquinas.SummaTheologiae (CausesAllInGenus IsMaximumIn)
open TruthCore.Case.Catholicism (MaximalCauseWithNoDistinctEsseCause)
open TruthCore.Causality.Round2PerfectionPrimacy
  (CausedInBeingByAnotherIsCreature CreatureEsseIsReceived)
open TruthCore.Causality.CausalMapsBatch1 (CausedPerfectionIsHad)
open TruthCore.Causality.DeiFiliusUnifiedRoute (CausedEsseIsReceived)
open TruthCore.Causality.CreatureSenses

/-- Strength order: the general premise (a caused perfection is had by its
effect, in every respect) gives its esse-restricted weak version. -/
theorem causedEsseIsHadFromCausedPerfection {B R : Type}
    (CausesIn : B → B → R → Prop) (InAct : B → R → Prop) (esse : R)
    (h : CausedPerfectionIsHad CausesIn InAct) :
    CausedEsseIsHad CausesIn InAct esse :=
  fun c x hc => h c x esse hc

/-- The CREATURE_2 → CREATURE_1 bridge, at its sense-fixed wrapper. Let c ≠ x
cause x's being (x is CREATURE_2). Take the maximum m of the Fourth-Way
consequence: it causes the being of every other being in act, and no being
distinct from it causes its being. So x ≠ m (else c, distinct from m, would cause
m's being); x is in act as to being (the weak premise); so m causes x's being, and
x is CREATURE_1 with m as its universal cause. -/
theorem causedInBeingByAnotherIsCreature1 {B R : Type}
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R)
    (hRoot : MaximalCauseWithNoDistinctEsseCause InAct MoreIn CausesIn esse)
    (hHad : CausedEsseIsHad CausesIn InAct esse) :
    CausedInBeingByAnotherIsCreature1 InAct CausesIn esse := by
  rintro x ⟨c, hne, hc⟩
  obtain ⟨m, _, hAll, hUncaused⟩ := hRoot
  have hxm : x ≠ m := by
    intro e
    subst e
    exact hUncaused c hne hc
  exact ⟨m, hAll, hxm, hAll x hxm (hHad c x hc)⟩

/-- Instantiation: the sense-fixed bridge gives the Creature-parametric legacy
statement `CausedInBeingByAnotherIsCreature` at `Creature := CREATURE_1`. A
re-presentation of the same content (a transcription by instantiation). -/
theorem causedInBeingByAnotherIsCreatureAtCreature1 {B R : Type}
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (h : CausedInBeingByAnotherIsCreature1 InAct CausesIn esse) :
    CausedInBeingByAnotherIsCreature CausesIn (IsCreatureOfUniversalCause InAct CausesIn esse) esse :=
  (causedInBeingByAnotherIsCreature_iff InAct CausesIn esse).mpr h

/-- Instantiation: the Creature-parametric legacy statement
`CreatureEsseIsReceived` read at `Creature := CREATURE_1` gives its sense-fixed
wrapper. A re-presentation of the same content (a transcription by
instantiation). -/
theorem creature1EsseIsReceivedAtCreature1 {B R P : Type}
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (EsseReceivedIn : B → P → Prop)
    (h : CreatureEsseIsReceived (IsCreatureOfUniversalCause InAct CausesIn esse) EsseReceivedIn) :
    Creature1EsseIsReceived InAct CausesIn esse EsseReceivedIn :=
  h

/-- The bridge of the unified Dei Filius route, derived through CREATURE_1:
whatever is CREATURE_2 is CREATURE_1 (the sense-fixed bridge), and the esse of
every CREATURE_1 is received in some principle (the sense-fixed q.7 a.2
reading). -/
theorem causedEsseIsReceivedThroughCreature1 {B R P : Type}
    (InAct : B → R → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (EsseReceivedIn : B → P → Prop)
    (hBridge : CausedInBeingByAnotherIsCreature1 InAct CausesIn esse)
    (hRecv : Creature1EsseIsReceived InAct CausesIn esse EsseReceivedIn) :
    CausedEsseIsReceived CausesIn esse EsseReceivedIn :=
  fun c x hne hc => hRecv x (hBridge x ⟨c, hne, hc⟩)

open TruthCore.Causality.CreatureSenses.Control in
/-- The controls: CREATURE_2 does not give CREATURE_1 without the bridge; the
weak premise is needed; the whole new bundle has a model with a caused being. -/
theorem controls : TruthCore.Causality.CreatureSenses.Control.Controls := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  -- (1)
  · exact ⟨Three.a, by decide, ⟨rfl, rfl⟩⟩
  · rintro ⟨g, hAll, _, hg⟩
    obtain ⟨rfl, -⟩ := hg
    exact absurd (hAll Three.c (by decide) trivial).2 (by decide)
  · intro h
    obtain ⟨g, hAll, _, hg⟩ := h Three.a Three.b (by decide) ⟨rfl, rfl⟩
    obtain ⟨rfl, -⟩ := hg
    exact absurd (hAll Three.c (by decide) trivial).2 (by decide)
  · intro _ _ _
    trivial
  · rintro ⟨m, _, hAll, _⟩
    cases m with
    | a => exact absurd (hAll Three.c (by decide) trivial).2 (by decide)
    | b => exact absurd (hAll Three.a (by decide) trivial).1 (by decide)
    | c => exact absurd (hAll Three.a (by decide) trivial).1 (by decide)
  -- (2)
  · refine ⟨Three.a, ⟨rfl, fun _ h => h⟩, ?_, ?_⟩
    · intro x hx hInAct
      exact absurd hInAct hx
    · intro d _ hd
      exact absurd hd.2 (by decide)
  · intro h
    have hc : omInAct Three.c () := h Three.b Three.c ⟨rfl, rfl⟩
    exact absurd hc (by decide)
  · intro h
    obtain ⟨g, hAll, _, hg⟩ := h Three.b Three.c (by decide) ⟨rfl, rfl⟩
    obtain ⟨rfl, -⟩ := hg
    exact absurd (hAll Three.a (by decide) rfl).2 (by decide)
  -- (3)
  · refine ⟨true, ⟨trivial, fun _ h => h⟩, ?_, ?_⟩
    · intro x hx _
      cases x with
      | false => exact ⟨rfl, rfl⟩
      | true => exact absurd rfl hx
    · intro c _ hc
      exact absurd hc.2 (by decide)
  · intro _ _ _
    trivial
  · intro c x _ hc
    obtain ⟨rfl, rfl⟩ := hc
    refine ⟨true, ?_, by decide, ⟨rfl, rfl⟩⟩
    intro y hy _
    cases y with
    | false => exact ⟨rfl, rfl⟩
    | true => exact absurd rfl hy
  · rintro x ⟨g, -, -, hg⟩
    exact ⟨(), hg.2⟩
  · intro c x _ hc
    exact ⟨(), hc.2⟩
  · exact ⟨true, by decide, ⟨rfl, rfl⟩⟩

end TruthCore.Results.Causality.CreatureSenses
