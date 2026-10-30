import TruthCore.Explanation.ExplanatoryAdequacy
import TruthCore.Results.Explanation.UltimateAdequacy.Solution

namespace TruthCore.Results.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.ExplanatoryAdequacy
open TruthCore.Explanation.PSRStrength
open TruthCore.German.Kant.CosmologicalInference

variable {W B F : Type}

/-! ## The general lemma -/

/-- Descent through contingent reasons: under foundedness, some contingent member
has only noncontingent reasons within `S`. Stated so that no case split is needed. -/
theorem forced {A : Arena W B F} {a : W} {S : F → Prop} {x : F}
    (hx : S x) (hc : Contingent A a x) (hf : Founded A a S)
    (H : ∀ c, S c → Contingent A a c →
      (∀ r, S r → A.explains a r c → ¬ Contingent A a r) → False) : False := by
  have key : ∀ f, S f → Contingent A a f → False := by
    intro f
    induction f using WellFounded.induction hf with
    | _ f ih =>
      intro hs hcf
      exact H f hs hcf (fun r hr he hcr => ih r ⟨hr, hs, he, hcr, hcf⟩ hr hcr)
  exact key x hx hc

theorem core_vary {A : Arena W B F} {a : W} {S : F → Prop} {x : F}
    (h : ReasonClosed A a S x) (hc : Contingent A a x) (hf : Founded A a S)
    (hv : AllReasonsVary A a S) : False :=
  forced h.explanandum hc hf (fun c hs hcc hn => by
    obtain ⟨r, he⟩ := h.covered c hs hcc
    exact hn r (h.closed r c hs he) he (hv r c hs hcc he))

theorem core_necessitate {A : Arena W B F} {a : W} {S : F → Prop} {x : F}
    (h : ReasonClosed A a S x) (hc : Contingent A a x) (hf : Founded A a S)
    (hn : AllReasonsNecessitate A a S) : False :=
  core_vary h hc hf (fun r f hs hcf he => by
    obtain ⟨_, v, hv, hnot⟩ := hcf
    exact ⟨h.truthful r (h.closed r f hs he), v, hv,
      fun hr => hnot (hn r f hs ⟨h.truthful f hs, v, hv, hnot⟩ he v hv hr)⟩)

theorem core_contrast {A : Arena W B F} {a : W} {S : F → Prop} {x : F}
    (h : ReasonClosed A a S x) (hc : Contingent A a x) (hf : Founded A a S)
    (ht : ContrastRelevant A a S) : False :=
  forced h.explanandum hc hf (fun c hs hcc hn => by
    obtain ⟨_, v, hv, hnot⟩ := hcc
    obtain ⟨r, hr, he, hrv⟩ := ht c hs ⟨h.truthful c hs, v, hv, hnot⟩ v hv hnot
    exact hn r hr he ⟨h.truthful r hr, v, hv, hrv⟩)

/-! ## Shared facts about the source accounts -/

theorem source_holds (p : Bool) (v : Nat) : groundHolds p v (.source true) := Or.inl rfl

theorem one_ne_zero' : (1 : Nat) ≠ 0 := fun h => Nat.noConfusion h

theorem ground_target_contingent (p : Bool) :
    Contingent (rival (groundHolds p) (GroundReason p)) 0 .target :=
  ⟨rfl, 1, trivial, one_ne_zero'⟩

theorem ground_source_not_contingent (p : Bool) (i : Bool) :
    ¬ Contingent (rival (groundHolds p) (GroundReason p)) 0 (.source i) := by
  rintro ⟨h, _, _, hn⟩
  exact hn h

theorem ground_closed : ReasonClosed ground 0 OneSource .target where
  explanandum := .target
  truthful := by
    intro f hf
    cases hf with
    | target => rfl
    | source => exact Or.inl rfl
  closed := by
    intro r f hf he
    cases hf with
    | target =>
      cases he with
      | toTarget i hi =>
        cases hi with
        | inl h => subst h; exact .source
        | inr h => exact Bool.noConfusion h
    | source => cases he
  covered := by
    intro f hf _
    cases hf with
    | target => exact ⟨.source true, .toTarget true (Or.inl rfl)⟩
    | source => exact ⟨.source true, by
        exact absurd ‹_› (ground_source_not_contingent false true)⟩
  nonCopy := by
    intro r f hf he hcf hco
    cases hf with
    | target =>
      cases he with
      | toTarget i hi => exact one_ne_zero' ((hco 1 trivial).1 hi)
    | source => cases he

theorem law_closed : ReasonClosed law 0 OneSource .target :=
  ⟨ground_closed.1, ground_closed.2, ground_closed.3, ground_closed.4, ground_closed.5⟩

theorem plural_closed : ReasonClosed plural 0 TwoSources .target where
  explanandum := .target
  truthful := by
    intro f hf
    cases hf with
    | target => rfl
    | source i => exact Or.inr rfl
  closed := by
    intro r f hf he
    cases hf with
    | target =>
      cases he with
      | toTarget i _ => exact .source i
    | source i => cases he
  covered := by
    intro f hf hc
    cases hf with
    | target => exact ⟨.source true, .toTarget true (Or.inl rfl)⟩
    | source i => exact absurd hc (ground_source_not_contingent true i)
  nonCopy := by
    intro r f hf he hcf hco
    cases hf with
    | target =>
      cases he with
      | toTarget i hi => exact one_ne_zero' ((hco 1 trivial).1 hi)
    | source i => cases he

/-! ## The chain -/

theorem chain_member_contingent (n : Nat) : Contingent chain 0 (.member n) :=
  ⟨Or.inl rfl, 1, trivial, by
    intro h
    cases h with
    | inl h => exact one_ne_zero' h
    | inr h => exact Nat.not_lt_zero (n + 1) (Nat.lt_of_succ_lt_succ h)⟩

theorem chain_target_contingent : Contingent chain 0 .target :=
  ⟨Nat.succ_ne_self 0 ∘ Eq.symm, 1, trivial, fun h => h rfl⟩

theorem chain_whole_contingent : Contingent chain 0 .whole :=
  ⟨rfl, 1, trivial, one_ne_zero'⟩

theorem member_at (n : Nat) : chainHolds (n + 3) (.member n) :=
  Or.inr (Nat.lt_succ_self (n + 2))

theorem member_fails (n v : Nat) (hv : v ≠ 0) (hle : v ≤ n + 2) : ¬ chainHolds v (.member n) := by
  intro h
  cases h with
  | inl h => exact hv h
  | inr h => exact Nat.not_lt_of_ge hle h

theorem chain_copy_target (hco : ∀ v, Access chain 0 v →
    (chain.holds v (.member 0) ↔ chain.holds v .target)) : False :=
  member_fails 0 2 (fun h => Nat.noConfusion h) (Nat.le_refl 2)
    ((hco 2 trivial).2 (Nat.succ_ne_self 1))

theorem chain_copy_step (n : Nat) (hco : ∀ v, Access chain 0 v →
    (chain.holds v (.member (n + 1)) ↔ chain.holds v (.member n))) : False :=
  member_fails (n + 1) (n + 3) (fun h => Nat.noConfusion h) (Nat.le_refl (n + 3))
    ((hco (n + 3) trivial).2 (member_at n))

theorem chain_copy_whole (m : Nat) (hco : ∀ v, Access chain 0 v →
    (chain.holds v (.member m) ↔ chain.holds v .whole)) : False :=
  (fun h => Nat.noConfusion h) ((hco (m + 3) trivial).1 (member_at m))

theorem chain_closed_members : ReasonClosed chain 0 Members .target where
  explanandum := .target
  truthful := by
    intro f hf
    cases hf with
    | target => exact Nat.succ_ne_self 0 ∘ Eq.symm
    | member n => exact Or.inl rfl
  closed := by
    intro r f hf he
    cases hf with
    | target => cases he with | toTarget => exact .member 0
    | member n => cases he with | step => exact .member (n + 1)
  covered := by
    intro f hf _
    cases hf with
    | target => exact ⟨.member 0, .toTarget⟩
    | member n => exact ⟨.member (n + 1), .step n⟩
  nonCopy := by
    intro r f hf he _ hco
    cases hf with
    | target => cases he with | toTarget => exact chain_copy_target hco
    | member n => cases he with | step => exact chain_copy_step n hco

theorem chain_closed_whole : ReasonClosed chain 0 MembersAndWhole .target where
  explanandum := .target
  truthful := by
    intro f hf
    cases hf with
    | target => exact Nat.succ_ne_self 0 ∘ Eq.symm
    | member n => exact Or.inl rfl
    | whole => rfl
  closed := by
    intro r f hf he
    cases hf with
    | target => cases he with | toTarget => exact .member 0
    | member n => cases he with | step => exact .member (n + 1)
    | whole => cases he with | toWhole m => exact .member m
  covered := by
    intro f hf _
    cases hf with
    | target => exact ⟨.member 0, .toTarget⟩
    | member n => exact ⟨.member (n + 1), .step n⟩
    | whole => exact ⟨.member 0, .toWhole 0⟩
  nonCopy := by
    intro r f hf he _ hco
    cases hf with
    | target => cases he with | toTarget => exact chain_copy_target hco
    | member n => cases he with | step => exact chain_copy_step n hco
    | whole => cases he with | toWhole m => exact chain_copy_whole m hco

theorem chain_vary : AllReasonsVary chain 0 Members := by
  intro r f hf _ he
  cases hf with
  | target => cases he with | toTarget => exact chain_member_contingent 0
  | member n => cases he with | step => exact chain_member_contingent (n + 1)

/-- A rival to member `n` is excluded by member `n + 1`. -/
theorem member_rival (n v : Nat) (hn : ¬ chainHolds v (.member n)) :
    v ≠ 0 ∧ v ≤ n + 2 :=
  ⟨fun h => hn (Or.inl h), Nat.le_of_not_lt (fun h => hn (Or.inr h))⟩

theorem target_rival (v : Nat) (hn : ¬ chainHolds v .target) : v = 1 :=
  Decidable.of_not_not hn

theorem chain_uniform : UniformContrast chain 0 Members := by
  intro f hf _
  cases hf with
  | target =>
    refine ⟨.member 0, .member 0, .toTarget, ?_⟩
    intro v _ hn
    have := target_rival v hn
    subst this
    exact member_fails 0 1 one_ne_zero' (Nat.le_succ 1)
  | member n =>
    refine ⟨.member (n + 1), .member (n + 1), .step n, ?_⟩
    intro v _ hn
    obtain ⟨h0, hle⟩ := member_rival n v hn
    exact member_fails (n + 1) v h0 (Nat.le_succ_of_le hle)

theorem chain_contrast : ContrastRelevant chain 0 Members := by
  intro f hf hc v hv hn
  obtain ⟨r, hr, he, hx⟩ := chain_uniform f hf hc
  exact ⟨r, hr, he, hx v hv hn⟩

theorem chain_contrast_whole : ContrastRelevant chain 0 MembersAndWhole := by
  intro f hf _ v _ hn
  cases hf with
  | target =>
    have := target_rival v hn
    subst this
    exact ⟨.member 0, .member 0, .toTarget, member_fails 0 1 one_ne_zero' (Nat.le_succ 1)⟩
  | member n =>
    obtain ⟨h0, hle⟩ := member_rival n v hn
    exact ⟨.member (n + 1), .member (n + 1), .step n,
      member_fails (n + 1) v h0 (Nat.le_succ_of_le hle)⟩
  | whole =>
    exact ⟨.member v, .member v, .toWhole v,
      member_fails v v hn (Nat.le_add_right v 2)⟩

theorem chain_not_uniform_whole : ¬ UniformContrast chain 0 MembersAndWhole := by
  intro h
  obtain ⟨r, _, he, hx⟩ := h .whole .whole chain_whole_contingent
  cases he with
  | toWhole m => exact hx (m + 3) trivial (fun h => Nat.noConfusion h) (member_at m)

/-! ## The brute, idle and necessitarian accounts -/

theorem brute_target_contingent : Contingent brute 0 .target :=
  ⟨rfl, 1, trivial, one_ne_zero'⟩

theorem brute_source_contingent : Contingent brute 0 (.source true) :=
  ⟨⟨rfl, Nat.zero_le 1⟩, 2, trivial, fun h => Nat.not_succ_le_self 1 h.2⟩

theorem brute_open (S : Fact → Prop) : ¬ ReasonClosed brute 0 S .target := by
  intro h
  obtain ⟨r, he⟩ := h.covered .target h.explanandum brute_target_contingent
  cases he
  have hs := h.closed _ _ h.explanandum (BruteReason.step)
  obtain ⟨r, he⟩ := h.covered _ hs brute_source_contingent
  cases he

theorem brute_founded : Founded brute 0 OneSource := by
  have src : Acc (ContingentReason brute 0 OneSource) (.source true) :=
    ⟨_, fun r hr => by cases hr.2.2.1⟩
  refine ⟨fun f => ?_⟩
  cases f with
  | target => exact ⟨_, fun r hr => by cases hr.2.2.1; exact src⟩
  | other => exact ⟨_, fun r hr => by cases hr.2.2.1⟩
  | source i => exact ⟨_, fun r hr => by cases hr.2.2.1⟩
  | member n => exact ⟨_, fun r hr => by cases hr.2.2.1⟩
  | whole => exact ⟨_, fun r hr => by cases hr.2.2.1⟩

theorem brute_vary : AllReasonsVary brute 0 OneSource := by
  intro r f _ _ he
  cases he
  exact brute_source_contingent

theorem idle_target_contingent : Contingent idle 0 .target :=
  ⟨rfl, 1, trivial, one_ne_zero'⟩

theorem idle_open (S : Fact → Prop) : ¬ ReasonClosed idle 0 S .target := by
  intro h
  obtain ⟨_, he⟩ := h.covered .target h.explanandum idle_target_contingent
  exact he

theorem necessity_not_contingent (f : Fact) : ¬ Contingent necessitarian 0 f := by
  rintro ⟨h, v, _, hn⟩
  cases f with
  | target => exact hn trivial
  | other => exact h
  | source i => exact hn h
  | member n => exact h
  | whole => exact h

theorem necessity_closed : ReasonClosed necessitarian 0 OneSource .target where
  explanandum := .target
  truthful := by
    intro f hf
    cases hf with
    | target => trivial
    | source => rfl
  closed := by
    intro r f hf he
    cases hf with
    | target => cases he with | step => exact .source
    | source => cases he
  covered := fun f _ hc => absurd hc (necessity_not_contingent f)
  nonCopy := fun _ f _ _ hc => absurd hc (necessity_not_contingent f)

theorem necessity_founded : Founded necessitarian 0 OneSource :=
  ⟨fun _ => ⟨_, fun _ hr => absurd hr.2.2.2.2 (necessity_not_contingent _)⟩⟩

theorem ground_founded : Founded ground 0 OneSource :=
  ⟨fun _ => ⟨_, fun r hr => by
    obtain ⟨_, _, he, hcr, _⟩ := hr
    cases he with
    | toTarget i _ => exact absurd hcr (ground_source_not_contingent false i)
    | toOther i _ _ hne => exact absurd rfl hne⟩⟩

theorem ground_not_vary : ¬ AllReasonsVary ground 0 OneSource := fun h =>
  ground_source_not_contingent false true
    (h _ _ .target (ground_target_contingent false) (.toTarget true (Or.inl rfl)))

/-- **Core.** -/
theorem core : Core :=
  ⟨fun _ _ _ _ _ _ _ h hc hf hv => core_vary h hc hf hv,
    fun _ _ _ _ _ _ _ h hc hf hv => core_necessitate h hc hf hv,
    fun _ _ _ _ _ _ _ h hc hf hv => core_contrast h hc hf hv,
    ⟨brute_open, brute_target_contingent, brute_founded, brute_vary⟩,
    ⟨chain_closed_members, chain_target_contingent,
      fun hf => core_vary chain_closed_members chain_target_contingent hf chain_vary, chain_vary⟩,
    ⟨ground_closed, ground_target_contingent false, ground_founded, ground_not_vary⟩,
    ⟨necessity_closed, necessity_not_contingent _, necessity_founded,
      fun _ f _ hc => absurd hc (necessity_not_contingent f)⟩⟩

/-! ## Comparison -/

theorem ground_no_contrast (S : Fact → Prop) (hS : S .target) : ¬ ContrastRelevant ground 0 S := by
  intro h
  obtain ⟨r, _, he, hr⟩ := h .target hS (ground_target_contingent false) 1 trivial one_ne_zero'
  cases he with
  | toTarget i hi => exact hr hi

theorem plural_no_contrast (S : Fact → Prop) (hS : S .target) : ¬ ContrastRelevant plural 0 S := by
  intro h
  obtain ⟨r, _, he, hr⟩ := h .target hS (ground_target_contingent true) 1 trivial one_ne_zero'
  cases he with
  | toTarget i hi => exact hr hi

theorem brute_no_contrast (S : Fact → Prop) (hS : S .target) : ¬ ContrastRelevant brute 0 S := by
  intro h
  obtain ⟨r, _, he, hr⟩ := h .target hS brute_target_contingent 1 trivial one_ne_zero'
  cases he
  exact hr ⟨rfl, Nat.le_refl 1⟩

theorem idle_no_contrast (S : Fact → Prop) (hS : S .target) : ¬ ContrastRelevant idle 0 S := by
  intro h
  obtain ⟨_, _, he, _⟩ := h .target hS idle_target_contingent 1 trivial one_ne_zero'
  exact he

theorem ground_two_way : TwoWay ground 0 OneSource := by
  intro f hf hc v _ hn
  cases hf with
  | target =>
    exact ⟨.source true, .other, .source, .toTarget true (Or.inl rfl), hn, fun h => h rfl,
      .toOther true v (Or.inl rfl) hn⟩
  | source => exact absurd hc (ground_source_not_contingent false true)

theorem plural_two_way : TwoWay plural 0 TwoSources := by
  intro f hf hc v _ hn
  cases hf with
  | target =>
    exact ⟨.source true, .other, .source true, .toTarget true (Or.inl rfl), hn, fun h => h rfl,
      .toOther true v (Or.inl rfl) hn⟩
  | source i => exact absurd hc (ground_source_not_contingent true i)

theorem chain_no_two_way (S : Fact → Prop) (hS : S .target) : ¬ TwoWay chain 0 S := by
  intro h
  obtain ⟨_, _, _, _, _, _, he⟩ :=
    h .target hS chain_target_contingent 1 trivial (fun hn => hn rfl)
  cases he

theorem brute_no_two_way (S : Fact → Prop) (hS : S .target) : ¬ TwoWay brute 0 S := by
  intro h
  obtain ⟨_, _, _, _, _, _, he⟩ := h .target hS brute_target_contingent 1 trivial one_ne_zero'
  cases he

theorem idle_no_two_way (S : Fact → Prop) (hS : S .target) : ¬ TwoWay idle 0 S := by
  intro h
  obtain ⟨_, _, _, _, _, _, he⟩ := h .target hS idle_target_contingent 1 trivial one_ne_zero'
  exact he

theorem closed_bare (A : Arena W B F) (a : W) (S : F → Prop) (x : F) :
    ReasonClosed A a S x ↔ ReasonClosed (bare A) a S x :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

theorem token_closed (A : Arena W B F) (a : W) (x : F) (hx : A.holds a x) :
    ReasonClosed (tokenExpand A) a (tokenAccount A a) (some x) where
  explanandum := hx
  truthful := by
    intro f hf
    cases f with
    | none => trivial
    | some f => exact hf
  closed := by
    intro r f _ he
    cases he
    trivial
  covered := by
    intro f _ hc
    cases f with
    | none =>
      obtain ⟨_, _, _, hn⟩ := hc
      exact absurd trivial hn
    | some f => exact ⟨none, .mk hc⟩
  nonCopy := by
    intro r f _ he hc hco
    cases he
    obtain ⟨_, v, hv, hn⟩ := hc
    exact hn ((hco v hv).1 trivial)

theorem token_no_contrast (A : Arena W B F) (a : W) (x : F) (S : Option F → Prop)
    (hS : S (some x)) (hc : Contingent A a x) : ¬ ContrastRelevant (tokenExpand A) a S := by
  intro h
  obtain ⟨hh, v, hv, hn⟩ := hc
  obtain ⟨r, _, he, hr⟩ := h (some x) hS ⟨hh, v, hv, hn⟩ v hv hn
  cases he
  exact hr trivial

theorem token_two_way (A : Arena W B F) (a : W)
    (hr : ∀ f v, Contingent A a f → Access A a v → ¬ A.holds v f →
      ∃ g, A.holds v g ∧ ¬ A.holds a g ∧ Contingent A v g) :
    TwoWay (tokenExpand A) a (tokenAccount A a) := by
  intro f _ hc v hv hn
  cases f with
  | none =>
    obtain ⟨_, _, _, hn'⟩ := hc
    exact absurd trivial hn'
  | some f =>
    obtain ⟨g, hg, hga, hcg⟩ := hr f v hc hv hn
    exact ⟨none, some g, trivial, .mk hc, hg, hga, .mk hcg⟩

theorem ground_being_stop : BeingStop ground 0 OneSource := by
  intro f hf hn
  cases hf with
  | target => exact absurd (ground_target_contingent false) hn
  | source => exact ⟨some true, rfl, fun _ _ => Or.inl rfl⟩

theorem plural_being_stop : BeingStop plural 0 TwoSources := by
  intro f hf hn
  cases hf with
  | target => exact absurd (ground_target_contingent true) hn
  | source i => exact ⟨some i, rfl, fun _ _ => Or.inr rfl⟩

theorem law_no_being_stop (S : Fact → Prop) (h : ReasonClosed law 0 S .target) :
    ¬ BeingStop law 0 S := by
  intro hb
  have hs : S (.source true) := h.closed _ _ h.explanandum (GroundReason.toTarget true (Or.inl rfl))
  obtain ⟨_, heq, _⟩ := hb _ hs (ground_source_not_contingent false true)
  exact Fact.noConfusion heq

theorem chain_being_stop : BeingStop chain 0 Members := by
  intro f hf hn
  cases hf with
  | target => exact absurd chain_target_contingent hn
  | member n => exact absurd (chain_member_contingent n) hn

theorem being_stop_forces (A : Arena W B F) (a : W) (S : F → Prop) (x : F)
    (h : ReasonClosed A a S x) (hc : Contingent A a x) (hf : Founded A a S)
    (hb : BeingStop A a S) : ¬ ∀ y, ¬ NecessaryAt A.ontic a y := by
  intro hno
  refine forced h.explanandum hc hf (fun c hs hcc hn => ?_)
  obtain ⟨r, he⟩ := h.covered c hs hcc
  have hr := h.closed r c hs he
  obtain ⟨y, _, hy⟩ := hb r hr (hn r hr he)
  exact hno y hy

/-! ## The #735 overlays -/

open TruthCore.Explanation.UltimateAdequacy in
theorem overlay_all_necessary (k : Kind) : ∃ S, ReasonClosed (overlay k true) false S 2 := by
  refine ⟨fun _ => True, ⟨trivial, fun _ _ => Or.inl rfl, fun _ _ _ _ => trivial, ?_, ?_⟩⟩
  · rintro f _ ⟨_, _, _, hn⟩
    exact absurd (Or.inr (Or.inl rfl)) hn
  · rintro _ f _ _ ⟨_, _, _, hn⟩
    exact absurd (Or.inr (Or.inl rfl)) hn

open TruthCore.Explanation.UltimateAdequacy in
theorem overlay_single : ∃ S, ReasonClosed (overlay .single false) false S 2 := by
  refine ⟨fun _ => True, ⟨trivial, fun _ _ => Or.inl rfl, fun _ _ _ _ => trivial, ?_, ?_⟩⟩
  · intro f _ hc
    cases f with
    | zero =>
      obtain ⟨_, _, _, hn⟩ := hc
      exact absurd (Or.inr (Or.inr rfl)) hn
    | succ n => exact ⟨0, Or.inl rfl, Or.inl rfl, n, trivial, rfl, Or.inl rfl⟩
  · intro r f _ he hc hco
    obtain ⟨_, _, g, _, _, hm⟩ := he
    obtain ⟨_, v, hv, hn⟩ := hc
    cases hm with
    | inl hr =>
      have hr' : r = 0 := hr
      subst hr'
      exact hn ((hco v hv).1 (Or.inr (Or.inr rfl)))
    | inr hr => exact hr

open TruthCore.Explanation.UltimateAdequacy in
theorem overlay_plural : ∃ S, ReasonClosed (overlay .plural false) false S 2 := by
  refine ⟨fun _ => True, ⟨trivial, fun _ _ => Or.inl rfl, fun _ _ _ _ => trivial, ?_, ?_⟩⟩
  · intro f _ hc
    obtain ⟨_, _, _, hn⟩ := hc
    cases f with
    | zero => exact absurd (Or.inr (Or.inr (Or.inl rfl))) hn
    | succ n =>
      cases n with
      | zero => exact absurd (Or.inr (Or.inr (Or.inr rfl))) hn
      | succ n => exact ⟨0, Or.inl rfl, Or.inl rfl, n, trivial, rfl, Or.inl (Or.inl rfl)⟩
  · intro r f _ he hc hco
    obtain ⟨_, _, g, _, _, hm⟩ := he
    obtain ⟨_, v, hv, hn⟩ := hc
    cases hm with
    | inl hr =>
      cases hr with
      | inl hr =>
        subst hr
        exact hn ((hco v hv).1 (Or.inr (Or.inr (Or.inl rfl))))
      | inr hr =>
        subst hr
        exact hn ((hco v hv).1 (Or.inr (Or.inr (Or.inr rfl))))
    | inr hr => exact hr

open TruthCore.Explanation.UltimateAdequacy in
theorem overlay_contingent (k : Kind) : Contingent (overlay k false) false 2 :=
  TruthCore.Results.Explanation.UltimateAdequacy.modal_contingent k

open TruthCore.Explanation.UltimateAdequacy in
theorem overlay_branch (S : Nat → Prop) : ¬ ReasonClosed (overlay .branch false) false S 2 := by
  intro h
  have he : (overlay .branch false).explains false 3 2 :=
    ⟨Or.inl rfl, Or.inl rfl, 1, trivial, rfl, Or.inl (Or.inr rfl)⟩
  refine h.nonCopy 3 2 h.explanandum he (overlay_contingent .branch) ?_
  intro v _
  cases v with
  | false => exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩
  | true =>
    constructor
    · rintro (h | h | h)
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
      · exact Nat.noConfusion h
    · rintro (h | h | h)
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
      · exact Nat.noConfusion h

open TruthCore.Explanation.UltimateAdequacy in
theorem overlay_chain (S : Nat → Prop) : ¬ ReasonClosed (overlay .chain false) false S 2 := by
  intro h
  have he : (overlay .chain false).explains false 3 2 :=
    ⟨Or.inl rfl, Or.inl rfl, 2, trivial, rfl, Or.inl (Or.inl rfl)⟩
  refine h.nonCopy 3 2 h.explanandum he (overlay_contingent .chain) ?_
  intro v _
  cases v with
  | false => exact ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩
  | true =>
    constructor
    · rintro (h | h | h)
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
      · exact False.elim h
    · rintro (h | h | h)
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
      · exact False.elim h

/-- **Comparison.** -/
theorem comparison : Comparison := by
  refine ⟨ground_closed, plural_closed, law_closed, chain_closed_whole, necessity_closed,
    brute_open, idle_open, ground_no_contrast, plural_no_contrast, ground_no_contrast,
    brute_no_contrast, idle_no_contrast, chain_contrast, chain_uniform, chain_contrast_whole,
    chain_not_uniform_whole, fun f _ hc => absurd hc (necessity_not_contingent f),
    ground_two_way, plural_two_way, ground_two_way,
    fun f _ hc => absurd hc (necessity_not_contingent f),
    chain_no_two_way, brute_no_two_way, idle_no_two_way,
    fun _ _ _ A a S x => ⟨closed_bare A a S x, Iff.rfl, Iff.rfl⟩,
    rfl, ?_, ?_, fun _ _ => rfl, fun _ _ => Or.inl rfl,
    fun _ _ _ A a x hx => ⟨rfl, fun _ _ => Iff.rfl, token_closed A a x hx⟩,
    fun _ _ _ A a x S hS hc => token_no_contrast A a x S hS hc,
    fun _ _ _ A a hr => token_two_way A a hr,
    token_closed brute 0 .target rfl,
    ground_being_stop, plural_being_stop, law_no_being_stop, chain_being_stop,
    fun _ _ _ A a S x h hc hf hb => being_stop_forces A a S x h hc hf hb,
    overlay_all_necessary, overlay_single, overlay_plural, overlay_branch, overlay_chain,
    TruthCore.Results.Explanation.UltimateAdequacy.chain_no_supply 2,
    TruthCore.Results.Explanation.UltimateAdequacy.plural_supply 2,
    TruthCore.Results.Explanation.UltimateAdequacy.plural_no_least⟩
  · intro _ h
    exact one_ne_zero' (h 1 trivial)
  · intro x h
    cases x with
    | none => exact (h 1 trivial) rfl
    | some i =>
      cases h 0 trivial

end TruthCore.Results.Explanation.ExplanatoryAdequacy
