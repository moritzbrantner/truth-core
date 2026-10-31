import TruthCore.Explanation.ExplanatorySymmetry
import TruthCore.Results.Explanation.ExplanatoryAdequacy.Solution

namespace TruthCore.Results.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.ExplanatorySymmetry
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.PSRStrength hiding ground
open TruthCore.Explanation.HistorySelection

variable {W B F : Type}

/-! ## The general lemmas -/

/-- A rival's net-selection blocks the opposite favouring at a world with the same base. -/
theorem no_opposite {X : Frame W B F} {base : F → Prop} {v w : W} {f g : F}
    (he : SameEvidence X.arena.holds base v w) (hf : BaseFixed X base)
    (hv : NetSelects X base v f g) (r : F) (hr : ProTanto X base w r g f) : False :=
  hv.2 r hr.1 ((he r hr.1).2 hr.2.1) ((hf v w r g f he hr.1).2 hr.2.2.2.2.2)

theorem core_pair {X : Frame W B F} {base O : F → Prop} {a v : W} {f : F}
    (he : SameEvidence X.arena.holds base a v) (hf : BaseFixed X base)
    (ha : SelectedAt X base O a) (hv : SelectedAt X base O v)
    (hex : ExhaustiveAt X.arena O v) (hcl : ExclusiveAt X.arena O a)
    (hO : O f) (hfa : X.arena.holds a f) (hfv : ¬ X.arena.holds v f) : False := by
  obtain ⟨g, hg, hgv⟩ := hex
  have hga : ¬ X.arena.holds a g := fun h => by
    have := hcl f g hO hg hfa h
    subst this
    exact hfv hgv
  obtain ⟨r, hr⟩ := (hv g f hg hO hgv hfv).1
  exact no_opposite he hf (ha f g hO hg hfa hga) r hr

theorem core_necessary {X : Frame W B F} {base O : F → Prop} {a : W} {f : F}
    (hn : NecessaryBase X.arena base a) (hf : BaseFixed X base)
    (hs : ∀ w, Worlds X.arena a w → SelectedAt X base O w)
    (hex : ∀ w, Worlds X.arena a w → ExhaustiveAt X.arena O w)
    (hcl : ∀ w, Worlds X.arena a w → ExclusiveAt X.arena O w)
    (hO : O f) : ¬ Contingent X.arena a f := by
  rintro ⟨hfa, v, hv, hfv⟩
  have ha : Worlds X.arena a a := Or.inl rfl
  have hw : Worlds X.arena a v := Or.inr hv
  exact core_pair (fun r hr => ⟨fun _ => hn r v hr hw, fun _ => hn r a hr ha⟩) hf
    (hs a ha) (hs v hw) (hex v hw) (hcl a ha) hO hfa hfv

/-! ## Facts about the models -/

theorem rival_cases {f : Fact} (h : Rival f) : f = .target ∨ f = .other := by
  cases h
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem same_ground (v w : Nat) : SameEvidence ground.holds oneSource v w := by
  rintro r rfl
  exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩

theorem ground_exhaustive (w : Nat) : ExhaustiveAt ground Rival w := by
  by_cases h : w = 0
  · exact ⟨.target, .target, h⟩
  · exact ⟨.other, .other, h⟩

theorem ground_exclusive (w : Nat) : ExclusiveAt ground Rival w := by
  intro f g hf hg h1 h2
  cases hf <;> cases hg
  · rfl
  · exact absurd h1 h2
  · exact absurd h2 h1
  · rfl

theorem one_ne : (1 : Nat) ≠ 0 := fun h => Nat.noConfusion h

theorem not_target_lt : ¬ targetFirst .target < targetFirst .other := Nat.not_lt_zero 1

theorem target_lt : targetFirst .other < targetFirst .target := Nat.zero_lt_one

theorem scalar_fixed {V : Type} [Preorder V] (A : Arena W B F) (q : F → V) (base : F → Prop) :
    BaseFixed (scalar A q) base :=
  fun _ _ _ _ _ _ _ => Iff.rfl

theorem perReason_fixed {V : Type} [Preorder V] (A : Arena W B F) (q : F → F → V)
    (base : F → Prop) : BaseFixed (perReason A q) base :=
  fun _ _ _ _ _ _ _ => Iff.rfl

theorem oneWay_at_zero : SelectedAt oneWay oneSource Rival 0 := by
  intro f g hf hg h1 h2
  cases hf <;> cases hg
  · exact absurd h1 h2
  · refine ⟨⟨.source true, rfl, Or.inl rfl, h1, h2, ?_, ?_⟩, ?_⟩
    · exact GroundReason.toTarget true (Or.inl rfl)
    · exact target_lt
    · intro _ _ _; exact not_target_lt
  · exact absurd rfl h1
  · exact absurd h1 h2

theorem oneWay_not_at_one : ¬ SelectedAt oneWay oneSource Rival 1 := by
  intro h
  obtain ⟨⟨r, _, _, _, _, _, hr⟩, _⟩ :=
    h .other .target .other .target one_ne (fun h : (1 : Nat) = 0 => one_ne h)
  exact not_target_lt hr

theorem settled_selected (w : Nat) : SelectedAt (settled ground) oneSource Rival w := by
  intro f g hf hg h1 h2
  refine ⟨⟨.source true, rfl, Or.inl rfl, h1, h2, ?_, h1, h2⟩, fun s _ _ hs => h2 hs.1⟩
  cases hf <;> cases hg
  · exact absurd h1 h2
  · cases (h1 : w = 0)
    exact GroundReason.toTarget true (Or.inl rfl)
  · exact GroundReason.toOther true w (Or.inl rfl) h1
  · exact absurd h1 h2

theorem settled_not_fixed : ¬ BaseFixed (settled ground) oneSource := by
  intro h
  have := (h 0 1 (.source true) .target .other (same_ground 0 1) rfl).1
    ⟨rfl, fun hh : (0 : Nat) ≠ 0 => hh rfl⟩
  exact one_ne this.1

theorem necessitarian_selected (w : Nat) :
    SelectedAt (scalar necessitarian targetFirst) oneSource Rival w := by
  intro f g hf hg h1 h2
  cases hf <;> cases hg
  · exact absurd h1 h2
  · refine ⟨⟨.source true, rfl, rfl, h1, h2, NecessityReason.step w, ?_⟩, ?_⟩
    · exact target_lt
    · intro _ _ _; exact not_target_lt
  · exact False.elim h1
  · exact absurd h1 h2

theorem varying_selected (w : Nat) : SelectedAt varying varyingBase Rival w := by
  intro f g hf hg h1 h2
  cases hf <;> cases hg
  · exact absurd h1 h2
  · refine ⟨?_, ?_⟩
    · rcases (h1 : w = 0 ∨ w = 2) with rfl | rfl
      · exact ⟨.member 0, Or.inl rfl, rfl, Or.inl rfl, h2, VaryingReason.zero, Nat.zero_lt_one⟩
      · exact ⟨.member 2, Or.inr (Or.inr rfl), rfl, Or.inr rfl, h2, VaryingReason.two,
          Nat.zero_lt_one⟩
    · rintro s (rfl | rfl | rfl) hs hlt
      · exact Nat.not_lt_zero _ hlt
      · have hw : w ≠ 0 ∧ w ≠ 2 := hs
        rcases (h1 : w = 0 ∨ w = 2) with h | h
        · exact hw.1 h
        · exact hw.2 h
      · exact Nat.not_lt_zero _ hlt
  · have hw : w ≠ 0 ∧ w ≠ 2 := h1
    refine ⟨⟨.member 1, Or.inr (Or.inl rfl), hw, h1, h2, VaryingReason.one w hw.1 hw.2,
      Nat.zero_lt_one⟩, ?_⟩
    rintro s (rfl | rfl | rfl) hs hlt
    · exact hw.1 hs
    · exact Nat.not_lt_zero _ hlt
    · exact hw.2 hs
  · exact absurd h1 h2

theorem varying_open (S : Fact → Prop) : ¬ ReasonClosed varying.arena 0 S .target := by
  intro h
  have hm : S (.member 0) := h.closed _ _ h.explanandum VaryingReason.zero
  have hc : Contingent varying.arena 0 (.member 0) :=
    ⟨rfl, 1, trivial, fun h : (1 : Nat) = 0 => one_ne h⟩
  obtain ⟨r, hr⟩ := h.covered _ hm hc
  cases hr

theorem overlap_selected (w : Nat) : SelectedAt overlap oneSource Rival w := by
  intro f g hf hg h1 h2
  cases hf <;> cases hg
  · exact absurd h1 h2
  · exact absurd trivial h2
  · refine ⟨⟨.source true, rfl, rfl, h1, h2, OverlapReason.step w h2, Nat.zero_lt_one⟩, ?_⟩
    intro _ _ _ hlt
    exact Nat.not_lt_zero _ hlt
  · exact absurd h1 h2

theorem core : TruthCore.Explanation.ExplanatorySymmetry.Core := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ he hf ha hv hex hcl hO hfa hfv =>
      core_pair he hf ha hv hex hcl hO hfa hfv,
    fun _ _ _ _ _ _ _ _ hn hf hs hex hcl hO => core_necessary hn hf hs hex hcl hO,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- varying reasons
    refine ⟨fun h => ?_, perReason_fixed _ _ _, varying_selected 0, varying_selected 1,
      ⟨.other, .other, one_ne, fun h : (1 : Nat) = 2 => Nat.noConfusion h (fun h => Nat.noConfusion h)⟩,
      ?_, .target, Or.inl rfl, ?_, ⟨rfl, 1, trivial, fun h : (1 : Nat) = 0 => one_ne h⟩,
      varying_open⟩
    · exact one_ne ((h (.member 0) (Or.inl rfl)).1 rfl)
    · intro f g hf hg h1 h2
      cases hf <;> cases hg
      · rfl
      · exact absurd rfl h2.1
      · exact absurd rfl h1.1
      · rfl
    · rintro (h | h)
      · exact one_ne h
      · exact Nat.noConfusion h (fun h => Nat.noConfusion h)
  · exact ⟨same_ground 0 1, settled_not_fixed, settled_selected 0, settled_selected 1,
      ground_exhaustive 1, ground_exclusive 0, .target, rfl, one_ne⟩
  · exact ⟨same_ground 0 1, scalar_fixed _ _ _, oneWay_at_zero, oneWay_not_at_one,
      ground_exhaustive 1, ground_exclusive 0, .target, rfl, one_ne⟩
  · exact ⟨same_ground 1 0, scalar_fixed _ _ _, oneWay_not_at_one, oneWay_at_zero,
      ground_exhaustive 0, ground_exclusive 1, .other, one_ne, fun h => h rfl⟩
  · refine ⟨?_, fun _ _ _ _ _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
    · rintro r rfl
      exact ⟨fun _ => trivial, fun _ => trivial⟩
    · rintro f g rfl rfl h1 h2
      exact absurd h1 h2
    · rintro f g rfl rfl h1 h2
      exact absurd h1 h2
    · rintro ⟨g, rfl, h⟩
      exact Bool.noConfusion (h : true = false)
    · rintro f g rfl rfl _ _
      rfl
    · exact fun h => Bool.noConfusion (h : true = false)
  · refine ⟨?_, scalar_fixed _ _ _, overlap_selected 0, overlap_selected 1,
      ⟨.other, .other, trivial⟩, ?_, .target, rfl, one_ne⟩
    · rintro r rfl
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    · intro h
      exact Fact.noConfusion (h .target .other .target .other rfl trivial)
  · refine ⟨same_ground 0 1, fun _ _ _ _ _ _ _ => Iff.rfl, ?_, ?_,
      ⟨.source true, rfl, Or.inl rfl⟩, ?_, ?_, rfl, one_ne⟩
    · rintro f g rfl rfl _ h2
      exact absurd (Or.inl rfl) h2
    · rintro f g rfl rfl _ h2
      exact absurd (Or.inl rfl) h2
    · rintro f g rfl rfl _ _
      rfl
    · intro h
      exact Fact.noConfusion (h : Fact.target = Fact.source true)
  · have hs : SameEvidence necessitarian.holds oneSource 0 1 := by
      rintro r rfl
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    refine ⟨hs, scalar_fixed _ _ _, necessitarian_selected 0, necessitarian_selected 1,
      ⟨.target, .target, trivial⟩, ?_, .other, fun h => h, fun h => h⟩
    intro f g hf hg h1 h2
    cases hf <;> cases hg
    · rfl
    · exact False.elim h2
    · exact False.elim h1
    · rfl
  · have hs : SameEvidence necessitarian.holds oneSource 0 1 := by
      rintro r rfl
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    refine ⟨hs, scalar_fixed _ _ _, necessitarian_selected 0, necessitarian_selected 1,
      ⟨.target, .target, trivial⟩, ?_, .target, trivial, trivial⟩
    intro f g hf hg h1 h2
    cases hf <;> cases hg
    · rfl
    · exact False.elim h2
    · exact False.elim h1
    · rfl

/-! ## Comparison -/

/-- Opposite favouring at worlds with the same base, from the two pro tanto instances. -/
theorem conflict {X : Frame W B F} {base : F → Prop} {v w : W} {r s f g : F}
    (hf : BaseFixed X base) (he : SameEvidence X.arena.holds base v w)
    (hv : ProTanto X base v r f g) (hw : ProTanto X base w s g f) :
    ¬ NetSelects X base v f g ∧ ¬ NetSelects X base w g f :=
  ⟨fun h => no_opposite he hf h s hw,
    fun h => no_opposite (fun t ht => (he t ht).symm) (fun a b c d e h' hc => hf a b c d e h' hc) h r hv⟩

theorem acting_marks : Marks acting twoSources Rival 0 where
  twoWay := by
    intro w _ f g hf hg h1 h2
    cases hf <;> cases hg
    · exact absurd h1 h2
    · cases (h1 : w = 0)
      exact ⟨.source true, Or.inl rfl, trivial, rfl, h2, ActingReason.sourceTarget,
        Nat.zero_lt_one⟩
    · exact ⟨.source false, Or.inr rfl, trivial, h1, h2, ActingReason.sourceOther w h1,
        Nat.zero_lt_one⟩
    · exact absurd h1 h2
  plural := ⟨.source true, .source false, .target, .other, Or.inl rfl, Or.inr rfl,
    fun h => Bool.noConfusion (Fact.source.inj h), Nat.zero_lt_one, Nat.zero_lt_one⟩
  interposed := by
    intro w f _ hf h1
    cases hf
    · cases (h1 : w = 0)
      refine ⟨.source true, .member 0, Or.inl rfl, trivial, ActingReason.sourceAct,
        ActingReason.actTarget, ?_⟩
      rintro v _ (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · exact Nat.noConfusion h
    · refine ⟨.source false, .member 1, Or.inr rfl, trivial, ActingReason.sourceRival w h1,
        ActingReason.actOther w h1, ?_⟩
      rintro v _ (⟨h, _⟩ | ⟨_, h⟩)
      · exact Nat.noConfusion h
      · exact h
  open_ := by
    rintro f hf ⟨h1, _⟩
    cases hf
    · exact ⟨.source true, 1, Or.inl rfl, ActingReason.sourceTarget, trivial, trivial,
        fun h : (1 : Nat) = 0 => one_ne h⟩
    · exact absurd rfl h1

theorem acting_pro_zero : ProTanto acting twoSources 0 (.source true) .target .other :=
  ⟨Or.inl rfl, trivial, rfl, fun h => h rfl, ActingReason.sourceTarget, Nat.zero_lt_one⟩

theorem acting_pro_one : ProTanto acting twoSources 1 (.source false) .other .target :=
  ⟨Or.inr rfl, trivial, one_ne, fun h : (1 : Nat) = 0 => one_ne h,
    ActingReason.sourceOther 1 one_ne, Nat.zero_lt_one⟩

theorem acting_same : SameEvidence acting.arena.holds twoSources 0 1 := by
  rintro r (rfl | rfl) <;> exact ⟨fun _ => trivial, fun _ => trivial⟩

theorem path_gap {W B F : Type} {A : Arena W B F} {a v : W} {r f : F}
    (hp : Relation.ReflTransGen (A.explains a) r f) (hr : A.holds v r) (hf : ¬ A.holds v f) :
    ¬ ∀ x y, A.explains a x y → A.holds v x → A.holds v y := by
  intro hall
  have key : ∀ y, Relation.ReflTransGen (A.explains a) r y → A.holds v y := by
    intro y hy
    induction hy with
    | refl => exact hr
    | tail _ hstep ih => exact hall _ _ hstep ih
  exact hf (key f hp)

theorem comparison : TruthCore.Explanation.ExplanatorySymmetry.Comparison := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ _ X base v w r f g hf ha he hv hw
    exact ha v r f g hv.1 hv.2.2.2.2.2 ((hf v w r g f he hv.1).2 hw.2.2.2.2.2)
  · refine ⟨fun _ _ _ _ _ _ _ => Iff.rfl, fun h => h 0 (.source true) .target .other rfl trivial trivial,
      ⟨rfl, Or.inl rfl, rfl, fun h => h rfl, GroundReason.toTarget true (Or.inl rfl), trivial⟩,
      ⟨rfl, Or.inl rfl, one_ne, fun h : (1 : Nat) = 0 => one_ne h,
        GroundReason.toOther true 1 (Or.inl rfl) one_ne, trivial⟩⟩
  · intro _ _ _ X base v w r s f g hf he hv hw
    exact conflict hf he hv hw
  · refine ⟨acting_marks, perReason_fixed _ _ _, ?_, ⟨rfl, 1, trivial, fun h : (1 : Nat) = 0 => one_ne h⟩,
      (conflict (perReason_fixed _ _ _) acting_same acting_pro_zero acting_pro_one).1,
      (conflict (perReason_fixed _ _ _) acting_same acting_pro_zero acting_pro_one).2, ?_⟩
    · rintro r _ (rfl | rfl) _ <;> exact trivial
    · intro p
      exact ⟨fun ⟨_, hp, _⟩ => hp, fun hp => ⟨some true, hp, Or.inl rfl⟩⟩
  · intro _ _ _ A a v r f hp hr hf
    exact path_gap hp hr hf
  · intro _ _ _ A v r c f hc hr hf
    exact ⟨hr, fun h => hf (hc h)⟩
  · intro _ _ _ _ _ A q base v w r s f g hv hw
    exact lt_asymm hv.2.2.2.2.2 hw.2.2.2.2.2
  · rintro ⟨q, hq⟩
    have h1 : q .other < q .target :=
      (hq 0 (.source true) .target .other (Or.inl rfl) .target .other).1 Nat.zero_lt_one
    have h2 : q .target < q .other :=
      (hq 0 (.source false) .other .target (Or.inr rfl) .other .target).1 Nat.zero_lt_one
    exact Nat.lt_asymm h1 h2
  · intro v r f g h
    exact Nat.lt_irrefl _ h.2.2.2.2.2
  · refine ⟨oneWay_at_zero .target .other .target .other rfl (fun h => h rfl), Or.inl rfl, one_ne, ?_⟩
    intro h
    obtain ⟨⟨r, _, _, _, _, _, hr⟩, _⟩ := h
    exact not_target_lt hr
  · intro _ _ _ X base O w f g hF hs hf hg
    refine ⟨fun ⟨r, _, hr⟩ => hF w r f g hr, fun ⟨h1, h2⟩ => ?_⟩
    obtain ⟨⟨r, hb, _, _, _, _, hr⟩, _⟩ := hs f g hf hg h1 h2
    exact ⟨r, hb, hr⟩
  · exact ⟨fun _ _ _ _ h => h, settled_selected⟩
  · intro _ _ _ A a r f h v hv hr
    exact absurd (h v hv) hr
  · rintro _ _ _ A a r f hr ⟨_, v, hv, hn⟩
    exact ⟨hr, v, hv, hn⟩
  · intro _ _ _ A a f v _ hr
    exact absurd trivial hr
  · intro _ _ _ A a S x hc hx hf he
    refine TruthCore.Results.Explanation.ExplanatoryAdequacy.core_vary hc hx hf ?_
    intro r f hs hcf hexp
    obtain ⟨_, v, hv, hn⟩ := he r f hs hcf hexp
    exact ⟨hc.truthful r (hc.closed r f hs hexp), v, hv, hn⟩
  · refine ⟨⟨?_, 2, trivial, ?_⟩, ?_⟩
    · intro v _ hr hv
      have hv0 : v = 0 := hv
      subst hv0
      exact hr ⟨rfl, Nat.zero_le 1⟩
    · intro h
      have := (h : true = true ∧ (2 : Nat) ≤ 1).2
      exact Nat.not_succ_le_self 1 this
    · intro h
      exact one_ne (h 1 trivial ⟨rfl, Nat.le_refl 1⟩)
  · intro _ _ _ A w f g hc hg
    exact ⟨rfl, trivial, hc.1, hg, TokenReason.mk hc, rfl⟩
  · intro φ base O w
    exact Iff.rfl

end TruthCore.Results.Explanation.ExplanatorySymmetry

