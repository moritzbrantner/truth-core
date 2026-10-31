import TruthCore.Alternatives.PhysicalGround
import TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.Solution
import TruthCore.Results.Causality.RootMultiplication.Solution
import TruthCore.Results.Comparison.MindPhysicalism.Solution
import TruthCore.Results.Explanation.ExplanatorySymmetry.Solution

namespace TruthCore.Results.Alternatives.PhysicalGround

open TruthCore.Alternatives.PhysicalGround
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)
open TruthCore.Case.Catholicism
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.PSRStrength hiding ground
open TruthCore.Explanation.HistorySelection
open TruthCore.Logic
open TruthCore.Results.Explanation.ExplanatorySymmetry
open TruthCore.Results.Explanation.ExplanatoryAdequacy (core_vary)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers (Capacity)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt ContingentAt Ontic)
open TruthCore.Causality.NecessarilyUnderived (NecessarilyUnderived NoExistingSupportAt)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers (existsAt response)
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual (alternatingFrame alternatingExists)
open TruthCore.Results.Comparison.MindPhysicalism (Point pointFrame allBased completeOfBase
  baseEffect candidateEffect baseNotOver effectPhysical basePhysical candidateNotPhysical)

variable {B R P : Type}

/-! ## Conditional consequences -/

theorem contains_formal {t : Table B R} {Q : R → Prop} {g x : B} {r : R}
    (h : Contains t Q) (hq : Q r) (hc : t.CausesIn g x t.esse) (hx : t.Formal x r) :
    t.Formal g r := by
  rcases h g x r hc (Or.inl hx) with h | h
  · exact h
  · exact (h.1 hq).elim

theorem maximum_immaterial (m : Route B R P) (g : B) (h : m.Structural) (hm : m.Maximum g) :
    ¬ m.Composite g ∧ ¬ m.MatterForm g ∧ ∀ y, ¬ m.ComponentOf g y := by
  have hs := TruthCore.Results.Case.Catholicism.StageTwo.GodIsSimple.godIsSimple (· = g)
    m.Composite m.InAct m.MoreIn m.CausesIn m.esse (fun _ e => e ▸ hm) h.uniting h.causeMore g rfl
  exact ⟨hs, fun hf => hs ((h.kinds g).1 hf),
    fun y hy => h.noComponent g y hy (h.firstBeing g hm)⟩

theorem maximum_intellect (m : Route B R P) (g : B) (h : m.Structural) (hm : m.Maximum g)
    (hi : m.Immaterial) : m.HasIntellect g :=
  TruthCore.Results.Case.Catholicism.StageTwo.GodHasIntellect.godHasIntellect (· = g)
    m.Composite m.MatterForm m.HasIntellect m.ComponentOf m.PriorSimply m.essenceOf m.esseOf
    m.InAct m.MoreIn m.CausesIn m.esse (fun _ e => e ▸ hm) h.uniting h.causeMore h.kinds
    h.noComponent h.firstBeing hi g rfl

theorem maximum_will (m : Route B R P) (g : B) (h : m.Structural) (hm : m.Maximum g)
    (hi : m.Immaterial) (hw : WillFollowsIntellectReading m.HasIntellect m.HasWill) :
    m.HasWill g :=
  TruthCore.Results.Case.Catholicism.StageTwo.GodHasWill.godHasWill (· = g)
    m.Composite m.MatterForm m.HasIntellect m.HasWill m.ComponentOf m.PriorSimply m.essenceOf
    m.esseOf m.InAct m.MoreIn m.CausesIn m.esse (fun _ e => e ▸ hm) h.uniting h.causeMore h.kinds
    h.noComponent h.firstBeing hi hw g rfl

theorem bearing_core {Occ Kind : Type} (c : Bearing Occ Kind B) (e : Occ) (hEM : ExcludedMiddle)
    (h1 : MP.Completeness c.frame) (h2 : MP.CausalInfluence c.frame)
    (h3 : MP.EachCauseNotAllOverdetermined c.frame) (hm : c.frame.Mental e)
    (hs : ¬ c.Composite (c.bearer e)) (hp : PhysicalBearersComposite c)
    (hr : RealizerSameBearer c) : False := by
  rcases allBased hEM c.frame h1 h2 h3 e hm with h | ⟨r, hrp, hre⟩
  · exact hs (hp e h)
  · exact hs (hr e r hre ▸ hp r hrp)

theorem state_differs {W F S : Type} {X : Frame W B F} (sf : StateFacts X S) {base O : F → Prop}
    {a v : W} {f : F} (hb : ∀ r, base r → ∃ s, r = sf.fact s) (hf : BaseFixed X base)
    (ha : SelectedAt X base O a) (hv : SelectedAt X base O v)
    (hex : ExhaustiveAt X.arena O v) (hcl : ExclusiveAt X.arena O a)
    (hO : O f) (hfa : X.arena.holds a f) (hfv : ¬ X.arena.holds v f) :
    sf.state a ≠ sf.state v := by
  intro he
  refine core_pair (fun r hr => ?_) hf ha hv hex hcl hO hfa hfv
  obtain ⟨s, rfl⟩ := hb r hr
  rw [sf.holds_fact, sf.holds_fact, he]

theorem core : TruthCore.Alternatives.PhysicalGround.Core := by
  refine ⟨fun _ _ _ _ _ _ _ h hq hc hx => contains_formal h hq hc hx,
    fun _ _ _ _ _ _ h hq hc hx => contains_formal h hq hc hx,
    fun _ _ _ m g h hm => maximum_immaterial m g h hm,
    fun _ _ _ m g h hm hi => maximum_intellect m g h hm hi,
    fun _ _ _ m g h hm hi hw => maximum_will m g h hm hi hw,
    fun _ _ _ c e hEM h1 h2 h3 hm hs hp hr => bearing_core c e hEM h1 h2 h3 hm hs hp hr,
    fun _ _ _ _ _ sf _ _ _ _ _ hb hf ha hv hex hcl hO hfa hfv =>
      state_differs sf hb hf ha hv hex hcl hO hfa hfv,
    fun _ _ _ _ _ sf a v hacc hne => ?_,
    fun _ _ _ _ _ _ _ _ h hc hf hv => core_vary h hc hf hv,
    fun _ _ _ _ _ hx he hm => ⟨hx _ hm, hx _ (he hm)⟩,
    fun _ _ _ _ g h v hv => ⟨g, h v hv⟩⟩
  exact ⟨(sf.holds_fact _ _).2 rfl, v, hacc, fun h => hne ((sf.holds_fact _ _).1 h)⟩

/-! ## Containment verdicts -/

theorem esse_not_pure_off (gm gb : Bool) (r : Perf) :
    ¬ IndependentlyPure (table gm gb false false) .ground r := by
  rintro ⟨x, hne, hc, hf⟩
  cases x <;> cases r <;> simp_all [table]

theorem pure_iff (gm gb a b : Bool) (r : Perf) :
    IndependentlyPure (table gm gb a b) .ground r ↔
      (a = true ∧ (r = .esse ∨ r = .mental)) ∨ (b = true ∧ (r = .esse ∨ r = .bodily)) := by
  constructor
  · rintro ⟨x, hne, hc, hf⟩
    cases x <;> cases r <;> simp_all [table]
  · rintro (⟨h, hr⟩ | ⟨h, hr⟩)
    · refine ⟨.simpleMind, by decide, by simp [table], ?_⟩
      rcases hr with rfl | rfl <;> simp [table, h]
    · refine ⟨.simpleBody, by decide, by simp [table], ?_⟩
      rcases hr with rfl | rfl <;> simp [table, h]

/-- The table fails a classification when the ground lacks a formal respect its effect has. -/
theorem not_contains (gm gb a b : Bool) (Q : Perf → Prop) (x : Node) (r : Perf)
    (hq : Q r) (hc : (table gm gb a b).CausesIn .ground x .esse)
    (hx : (table gm gb a b).Formal x r) (hg : ¬ (table gm gb a b).Formal .ground r) :
    ¬ Contains (table gm gb a b) Q :=
  fun h => hg (contains_formal h hq hc hx)

/-- A classification of the table is met when the ground has formally what it classifies. -/
theorem contains_of (gm gb a b : Bool) (Q : Perf → Prop)
    (h : ∀ r, Q r → (table gm gb a b).Formal .ground r) : Contains (table gm gb a b) Q := by
  intro c x r hc _
  by_cases hq : Q r
  · cases c
    · exact Or.inl (h r hq)
    all_goals (cases x <;> simp [table] at hc)
  · cases c
    · exact Or.inr ⟨hq, by simp [table]⟩
    all_goals (cases x <;> simp [table] at hc)

theorem containment :
    ((rival false false).CausesIn = (classical false false).CausesIn ∧
      (rival true false).CausesIn = (classical true false).CausesIn ∧
      (rival false true).CausesIn = (classical false true).CausesIn) ∧
    (¬ Contains (rival false false) everyRespect ∧ ¬ Contains (classical false false) everyRespect) ∧
    (Contains (rival false false) onlyEsse ∧ Contains (classical false false) onlyEsse) ∧
    (Contains (classical false false) withMental ∧ ¬ Contains (rival false false) withMental) ∧
    (Contains (rival false false) withBodily ∧ ¬ Contains (classical false false) withBodily) ∧
    (Contains (rival false false) (IndependentlyPure (rival false false) .ground) ∧
      Contains (classical false false) (IndependentlyPure (classical false false) .ground)) ∧
    (Contains (classical true false) (IndependentlyPure (classical true false) .ground) ∧
      ¬ Contains (rival true false) (IndependentlyPure (rival true false) .ground)) ∧
    (Contains (rival false true) (IndependentlyPure (rival false true) .ground) ∧
      ¬ Contains (classical false true) (IndependentlyPure (classical false true) .ground)) ∧
    (¬ Contains (rival true true) (IndependentlyPure (rival true true) .ground) ∧
      ¬ Contains (classical true true) (IndependentlyPure (classical true true) .ground)) := by
  have mentalNo : ∀ a b (Q : Perf → Prop), Q .mental → ¬ Contains (rival a b) Q :=
    fun a b Q hq => not_contains _ _ _ _ Q .mind .mental hq (by simp [table]) (by simp [table])
      (by simp [table])
  have bodilyNo : ∀ a b (Q : Perf → Prop), Q .bodily → ¬ Contains (classical a b) Q :=
    fun a b Q hq => not_contains _ _ _ _ Q .mind .bodily hq (by simp [table]) (by simp [table])
      (by simp [table])
  have okRival : ∀ a b (Q : Perf → Prop), ¬ Q .mental → Contains (rival a b) Q := fun a b Q hq =>
    contains_of _ _ _ _ Q fun r hr => by
      cases r
      · simp [table]
      · exact (hq hr).elim
      · simp [table]
  have okClassical : ∀ a b (Q : Perf → Prop), ¬ Q .bodily → Contains (classical a b) Q :=
    fun a b Q hq => contains_of _ _ _ _ Q fun r hr => by
      cases r
      · simp [table]
      · simp [table]
      · exact (hq hr).elim
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨mentalNo _ _ _ trivial, bodilyNo _ _ _ trivial⟩,
    ⟨okRival _ _ _ (by simp [onlyEsse]), okClassical _ _ _ (by simp [onlyEsse])⟩,
    ⟨okClassical _ _ _ (by simp [withMental]), mentalNo _ _ _ (by simp [withMental])⟩,
    ⟨okRival _ _ _ (by simp [withBodily]), bodilyNo _ _ _ (by simp [withBodily])⟩,
    ⟨okRival _ _ _ (esse_not_pure_off _ _ _), okClassical _ _ _ (esse_not_pure_off _ _ _)⟩,
    ⟨okClassical _ _ _ ?_, mentalNo _ _ _ ?_⟩, ⟨okRival _ _ _ ?_, bodilyNo _ _ _ ?_⟩,
    ⟨mentalNo _ _ _ ?_, bodilyNo _ _ _ ?_⟩⟩ <;> simp [pure_iff]

/-! ## Route verdicts -/

macro "route_tac" : tactic => `(tactic| (
  simp [route2, Route.Maximum, Route.Immaterial, IsMaximumIn, CompositeHasAUnitingCauseReading,
    CauseOfQualityInAnotherIsMoreSuchReading, MatterFormAndEsseEssenceAreCompositionsReading,
    NoComponentIsFirstBeingReading, MaximumInBeingIsFirstBeing, IsFirstBeing,
    ImmaterialIsIntellectualReading, WillFollowsIntellectReading, Bool.forall_bool,
    Bool.exists_bool]))

theorem routes :
    (let m := route2 False True False True True False False True False True False;
      m.Structural ∧ m.Maximum false ∧ m.Immaterial ∧ m.HasIntellect false ∧
      WillFollowsIntellectReading m.HasIntellect m.HasWill ∧ m.HasWill false) ∧
    (let m := route2 True True True True False False False True False True False;
      ¬ CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
      CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
      MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
      NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
      MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
      m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
    (let m := route2 True True True True False False True True False False False;
      CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
      ¬ CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
      MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
      NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
      MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
      m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
    (let m := route2 True True False False False False False False False False False;
      CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
      CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
      ¬ MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
      NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
      MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
      m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
    (let m := route2 False True False True False True False True False True False;
      CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
      CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
      MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
      ¬ NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
      MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
      m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
    (let m := route2 False True False True False True False True False True True;
      CompositeHasAUnitingCauseReading m.Composite m.CausesIn m.esse ∧
      CauseOfQualityInAnotherIsMoreSuchReading m.CausesIn m.MoreIn ∧
      MatterFormAndEsseEssenceAreCompositionsReading m.MatterForm m.Composite m.essenceOf m.esseOf ∧
      NoComponentIsFirstBeingReading m.ComponentOf m.PriorSimply ∧
      ¬ MaximumInBeingIsFirstBeing m.InAct m.MoreIn m.esse m.PriorSimply ∧
      m.Maximum false ∧ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
    (let m := route2 False True False True False False False True False True False;
      m.Structural ∧ m.Maximum false ∧ ¬ m.Immaterial ∧ ¬ m.HasIntellect false) ∧
    (endless.Structural ∧ ¬ endless.Maximum 0 ∧ endless.Immaterial ∧ ¬ endless.HasIntellect 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> route_tac
  iterate 5
    · dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> route_tac
  · dsimp only
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> route_tac
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · exact fun x _ => ⟨x + 1, by omega, rfl⟩
    · exact fun y x _ _ h => h
    · exact fun _ => ⟨fun _ => trivial, fun _ => trivial⟩
    · exact fun _ _ h => h.elim
    · intro m hm
      exact (hm.2 (m + 1) rfl).elim
    · exact fun hm => hm.2 1 rfl
    · exact fun _ h => (h trivial).elim
    · exact fun h => h

/-! ## Bearer verdicts -/

open TruthCore.Results.Comparison.MindPhysicalism in
/-- `candidate` borne by the noncomposite `true`, and the other points by composite `false`. -/
def pointBearing (f : TruthCore.Alternatives.MindPhysicalism.Frame Point Bool) :
    Bearing Point Bool Bool where
  frame := f
  bearer | .candidate => true | _ => false
  Composite := fun b => b = false

open TruthCore.Results.Comparison.MindPhysicalism in
/-- All three points borne by composite `false`. -/
def worldBearing (f : TruthCore.Alternatives.MindPhysicalism.Frame Point Bool) :
    Bearing Point Bool Bool where
  frame := f
  bearer := fun _ => false
  Composite := fun b => b = false

open TruthCore.Results.Comparison.MindPhysicalism
open TruthCore.Results.Comparison.MindPhysicalism.Point

/-- With a nonphysical candidate, the bearing's physical points are all composite. -/
theorem pointBearersComposite (a b d e g : Prop) :
    PhysicalBearersComposite (pointBearing (pointFrame a b False d e g)) := by
  intro x hx
  cases x with
  | candidate => exact (candidateNotPhysical _ _ _ _ _ hx).elim
  | base => rfl
  | effect => rfl

theorem pointNoRealizer (a b c d e : Prop) :
    RealizerSameBearer (pointBearing (pointFrame a b c d e False)) := by
  intro x r h
  cases x <;> cases r <;> exact h.elim

/-- The candidate is the only mental point when the base is not, and it has the effect. -/
theorem candidateInfluence (b c e g : Prop) (hb : ¬ b) :
    MP.CausalInfluence (pointFrame True b c True e g) := by
  intro x hx
  cases x with
  | candidate => exact ⟨effect, candidateEffect _ _ _ _ _⟩
  | base => exact (hb hx).elim
  | effect => exact hx.elim

/-- Point-frame distributive premise 3, given the candidate's effect is not overdetermined. -/
theorem candidateEach (c e g : Prop)
    (h : ¬ (pointFrame True False c True e g).Overdetermines candidate effect) :
    MP.EachCauseNotAllOverdetermined (pointFrame True False c True e g) := by
  intro x hx _ hAll
  cases x with
  | candidate => exact h (hAll effect (candidateEffect _ _ _ _ _))
  | base => exact hx
  | effect => exact hx

theorem bearers :
    (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), ¬ MP.Completeness c.frame ∧
      MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
      ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
    (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
      ¬ MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
      ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
    (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
      MP.CausalInfluence c.frame ∧ ¬ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
      ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
    (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
      MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ ¬ c.frame.Mental e ∧
      ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
    (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
      MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
      c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
    (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
      MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
      ¬ c.Composite (c.bearer e) ∧ ¬ PhysicalBearersComposite c ∧ RealizerSameBearer c) ∧
    (∃ (Occ Kind B : Type) (c : Bearing Occ Kind B) (e : Occ), MP.Completeness c.frame ∧
      MP.CausalInfluence c.frame ∧ MP.EachCauseNotAllOverdetermined c.frame ∧ c.frame.Mental e ∧
      ¬ c.Composite (c.bearer e) ∧ PhysicalBearersComposite c ∧ ¬ RealizerSameBearer c) := by
  have simple : ∀ f, ¬ (pointBearing f).Composite ((pointBearing f).bearer candidate) := by
    intro f
    simp [pointBearing]
  have realized : ∀ c, ¬ (pointFrame True False c True True True).Overdetermines candidate effect :=
    fun c h => h.2.2 (Or.inr ⟨base, ⟨basePhysical _ _ _ _ _ _, trivial⟩, trivial⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Point, Bool, Bool, pointBearing (pointFrame True False False True False False),
      candidate, ?_, candidateInfluence _ _ _ _ id, candidateEach _ _ _ ?_, trivial, simple _,
      pointBearersComposite _ _ _ _ _, pointNoRealizer _ _ _ _ _⟩
    · intro h
      rcases h effect (effectPhysical _ _ _ _ _ _) trivial with h | h
      · exact candidateNotPhysical _ _ _ _ _ h.1.1
      · exact h.2
    · intro h
      rcases h.2.1 with h | h
      · exact candidateNotPhysical _ _ _ _ _ h.1.1
      · exact h.2
  · refine ⟨Point, Bool, Bool, pointBearing (pointFrame True False False False True False),
      candidate, completeOfBase _ _ _ _ _, ?_, ?_, trivial, simple _,
      pointBearersComposite _ _ _ _ _, pointNoRealizer _ _ _ _ _⟩
    · intro h
      obtain ⟨x, hx⟩ := h candidate trivial
      cases effectOf hx
      exact hx.2.2
    · intro x hx ⟨y, hy⟩
      cases x with
      | candidate =>
        cases effectOf hy
        exact (hy.2.2).elim
      | base => exact hx.elim
      | effect => exact hx.elim
  · refine ⟨Point, Bool, Bool, pointBearing (pointFrame True False False True True False),
      candidate, completeOfBase _ _ _ _ _, candidateInfluence _ _ _ _ id, ?_, trivial, simple _,
      pointBearersComposite _ _ _ _ _, pointNoRealizer _ _ _ _ _⟩
    intro h
    refine h candidate trivial ⟨effect, candidateEffect _ _ _ _ _⟩ (fun x hx => ?_)
    cases effectOf hx
    exact candidateOverdetermines
  · refine ⟨Point, Bool, Bool, pointBearing (pointFrame False False False False True False),
      candidate, completeOfBase _ _ _ _ _, ?_, ?_, id, simple _,
      pointBearersComposite _ _ _ _ _, pointNoRealizer _ _ _ _ _⟩
    · intro x hx
      cases x <;> exact hx.elim
    · intro x hx
      cases x <;> exact hx.elim
  · refine ⟨Point, Bool, Bool, worldBearing (pointFrame True False False True True True),
      candidate, completeOfBase _ _ _ _ _, candidateInfluence _ _ _ _ id,
      candidateEach _ _ _ (realized _), trivial, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩
  · refine ⟨Point, Bool, Bool, pointBearing (pointFrame True False True True True False),
      candidate, completeOfBase _ _ _ _ _, candidateInfluence _ _ _ _ id,
      candidateEach _ _ _ ?_, trivial, simple _, ?_, pointNoRealizer _ _ _ _ _⟩
    · exact fun h => h.2.2 (Or.inl ⟨⟨true, trivial, trivial⟩, trivial⟩)
    · intro h
      exact simple _ (h candidate ⟨true, trivial, trivial⟩)
  · refine ⟨Point, Bool, Bool, pointBearing (pointFrame True False False True True True),
      candidate, completeOfBase _ _ _ _ _, candidateInfluence _ _ _ _ id,
      candidateEach _ _ _ (realized _), trivial, simple _, pointBearersComposite _ _ _ _ _, ?_⟩
    intro h
    exact absurd (h candidate base trivial) (by simp [pointBearing])

/-! ## State, capacity, roots -/

/-- The state of `varying`: which member holds. -/
def varyingState (w : Nat) : Nat := if w = 0 then 0 else if w = 2 then 2 else 1

/-- `varying` with `member n` as its state facts. -/
def varyingFacts : StateFacts varying Nat where
  state := varyingState
  fact := .member
  holds_fact := by
    intro v s
    show varyingHolds v (.member s) ↔ _
    rcases s with _ | _ | _ | s <;> by_cases h0 : v = 0 <;> by_cases h2 : v = 2 <;>
      simp_all [varyingHolds, varyingState]

/-- `oneWay` with the source fact as its one state fact. -/
def oneWayFacts : StateFacts oneWay Unit where
  state := fun _ => ()
  fact := fun _ => .source true
  holds_fact := by
    intro v s
    exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩

/-- A response on `ground`: the source activates the target's bearer at world `0`. -/
def groundResponse : Option Bool → Option Bool → Nat → Bool → Bool :=
  fun x y w on => x == some true && y == none && w == 0 && on

macro "ladder_tac" : tactic => `(tactic| (
  simp [route2, Route.Maximum, Route.Immaterial, Route.Structural, Route.supports, IsMaximumIn,
    CompositeHasAUnitingCauseReading, CauseOfQualityInAnotherIsMoreSuchReading,
    MatterFormAndEsseEssenceAreCompositionsReading, NoComponentIsFirstBeingReading,
    MaximumInBeingIsFirstBeing, IsFirstBeing, ImmaterialIsIntellectualReading,
    WillFollowsIntellectReading, Bool.forall_bool, Bool.exists_bool]))

theorem signature_of (m : Route Bool Unit Unit) (h : ∀ y, ¬ m.CausesIn y false m.esse)
    (hc : m.CausesIn false true m.esse) : Signature m := by
  have hn : ∀ w, NoExistingSupportAt powers m.supports w false := fun _ y _ => h y
  have hnec : NecessaryAt powers false false := fun _ _ => Or.inl rfl
  have hcap : ∀ w, Capacity alternatingFrame existsAt response false w := fun _ =>
    ⟨true, trivial, Or.inl rfl, true, Or.inr rfl, by decide, by decide⟩
  exact ⟨Or.inl rfl, hnec, hn, ⟨false, Or.inl rfl, hnec, hn⟩, hcap, hc, Or.inr rfl,
    false, trivial, by simp [powers, existsAt]⟩

theorem ladder :
    (Signature noMaximum ∧ noMaximum.Structural ∧ ¬ noMaximum.Maximum false ∧ noMaximum.Immaterial ∧
      ¬ noMaximum.HasIntellect false) ∧
    (Signature compositeRoot ∧ compositeRoot.Maximum false ∧ compositeRoot.Composite false ∧
      compositeRoot.MatterForm false ∧ (∀ y, ¬ compositeRoot.CausesIn y false compositeRoot.esse) ∧
      ¬ CompositeHasAUnitingCauseReading compositeRoot.Composite compositeRoot.CausesIn
        compositeRoot.esse ∧ ¬ compositeRoot.HasIntellect false) ∧
    (Signature simpleImpersonal ∧ simpleImpersonal.Structural ∧ simpleImpersonal.Maximum false ∧
      ¬ simpleImpersonal.Composite false ∧ ¬ simpleImpersonal.MatterForm false ∧
      ¬ simpleImpersonal.Immaterial ∧ ¬ simpleImpersonal.HasIntellect false) ∧
    (Signature willless ∧ willless.Structural ∧ willless.Maximum false ∧ willless.Immaterial ∧
      willless.HasIntellect false ∧ ¬ WillFollowsIntellectReading willless.HasIntellect willless.HasWill ∧
      ¬ willless.HasWill false) ∧
    (Signature classicalRoute ∧ classicalRoute.Structural ∧ classicalRoute.Maximum false ∧
      classicalRoute.Immaterial ∧ classicalRoute.HasIntellect false ∧ classicalRoute.HasWill false) := by
  refine ⟨⟨signature_of _ (by ladder_tac) (by ladder_tac), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
    ⟨signature_of _ (by ladder_tac) (by ladder_tac), ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨signature_of _ (by ladder_tac) (by ladder_tac), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨signature_of _ (by ladder_tac) (by ladder_tac), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨signature_of _ (by ladder_tac) (by ladder_tac), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩ <;> ladder_tac

theorem coverage :
    (SomethingNecessarily powers false ∧ SomethingNecessarily rotating false ∧
      (∀ x, ¬ NecessaryAt rotating false x) ∧ ¬ SomethingNecessarily law.ontic 0 ∧
      ¬ Explained ground 0 (.source true)) ∧
    (Contingent ground 0 .target ∧ ground.explains 0 (.source true) .target ∧
      ground.holds 1 (.source true) ∧ ¬ ground.holds 1 .target ∧
      NecessaryAt idle.ontic 0 (some true) ∧ Contingent idle 0 .target ∧ ¬ Explained idle 0 .target) ∧
    (NecessaryAt (onlyActual true) false false ∧ ¬ NecessaryAt (onlyActual false) false false ∧
      (onlyActual true).ExistsAt = (onlyActual false).ExistsAt) ∧
    (Marks acting twoSources Rival 0 ∧ MarksRequirePerson acting twoSources Rival 0 (fun _ => True) ∧
      ¬ MarksRequirePerson acting twoSources Rival 0 (fun _ => False)) := by
  have hM := comparison.2.2.2.1.1
  have hP := comparison.2.2.2.1.2.2.2.2.2.2
  refine ⟨⟨fun _ _ => ⟨false, Or.inl rfl⟩, fun v _ => ⟨v, rfl⟩, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, rfl⟩,
    hM, fun _ => (hP True).2 trivial, fun h => (hP False).1 (h hM)⟩
  · intro x h
    cases x
    · exact Bool.noConfusion (h true trivial)
    · exact Bool.noConfusion (h false trivial)
  · intro h
    obtain ⟨_, hx⟩ := h 1 trivial
    cases (hx : (1 : Nat) = 0)
  · rintro ⟨r, hr⟩
    cases hr
  · exact ⟨rfl, 1, trivial, fun h => by cases (h : (1 : Nat) = 0)⟩
  · exact .toTarget true (Or.inl rfl)
  · exact Or.inl rfl
  · exact fun h => by cases (h : (1 : Nat) = 0)
  · exact fun _ _ => rfl
  · exact ⟨rfl, 1, trivial, fun h => by cases (h : (1 : Nat) = 0)⟩
  · rintro ⟨r, hr⟩
    exact hr
  · intro v hv
    cases hv with
    | inl h => cases h
    | inr h => subst h; exact ⟨rfl, rfl⟩
  · intro h
    exact absurd (h true (Or.inl rfl)).1 (by decide)

theorem verdicts : TruthCore.Alternatives.PhysicalGround.Verdicts := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := containment
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8⟩ := routes
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := bearers
  obtain ⟨l1, l2, l3, l4, l5⟩ := ladder
  obtain ⟨v1, v2, v3, v4⟩ := coverage
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, r1, r2, r3, r4, r5, r6, r7, r8, b1, b2, b3, b4, b5,
    b6, b7, ⟨varyingFacts, ?_, ?_, perReason_fixed _ _ _, varying_selected 0, varying_selected 1,
    ?_, varying_open⟩, ⟨oneWayFacts, ?_, rfl, scalar_fixed _ _ _, oneWay_at_zero,
    oneWay_not_at_one⟩, ⟨groundResponse, ?_, ?_⟩, ?_, ?_, fun _ _ _ _ => Iff.rfl, ?_, ?_,
    l1, l2, l3, l4, l5, v1, v2, v3, v4⟩
  · rintro r (rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · decide
  · refine ⟨(varyingFacts.holds_fact _ _).2 rfl, 1, trivial, fun h => ?_⟩
    have := (varyingFacts.holds_fact _ _).1 h
    exact absurd this (by decide)
  · rintro r rfl
    exact ⟨(), rfl⟩
  · intro v _
    exact Or.inl rfl
  · intro w
    refine ⟨0, trivial, Or.inl rfl, none, rfl, by decide, ?_⟩
    decide
  · rintro _ x w ⟨_, _, _, y, _, h, _⟩
    exact h rfl
  · intro x h
    have : (1 : Nat) = 0 := h 1 trivial
    cases this
  · exact (TruthCore.Results.Causality.RootMultiplication.controls).1
  · exact ⟨fun h => h () trivial trivial, fun _ => trivial⟩

end TruthCore.Results.Alternatives.PhysicalGround
