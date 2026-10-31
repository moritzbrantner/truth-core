import TruthCore.Explanation.BCCFDerivative

namespace TruthCore.Results.Explanation.BCCFDerivative
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.BCCFDerivative

variable {W B F : Type}

/-! ## General theorems -/

/-- The totality argument over a class `D`. `t` is not assumed to be in `D`: a
contingent reason of `t` is a reason of the direct conjunct `c`, so closure at `c`
puts it in `D`, which makes it a conjunct of `t`. -/
theorem totality_collapse (A : Arena W B F) (G : Plural W F) (a : W) (D : F → Prop) (t c : F)
    (hs : ConjunctSound A) (hf : PFactive A G) (hn : PNecessitating A G)
    (hd : DistributesAt A G a t) (hi : PartIrreflexive A G) (hb : Bivalent A)
    (hcl : ClosedUnderReasons A G a D) (ht : DirectAggregate A a D t) (hD : D c)
    (hc : Contingent A a c) (hcov : Covered G a t) : False := by
  obtain ⟨Xs, hG⟩ := hcov
  have hct := ht.2 c hD hc
  obtain ⟨_, v, hv, hcv⟩ := hc
  apply hcv
  apply hs c t v hct
  apply hn a Xs t hG v hv
  intro x hx
  refine (hb v x).elim id fun hxv => False.elim ?_
  have hxc : Contingent A a x := ⟨(hf a Xs t hG).1 x hx, v, hv, hxv⟩
  have hDx := hcl c Xs x hD (hd Xs c hG hct) hx hxc
  exact hi a Xs x hxc (hd Xs x hG (ht.2 x hDx hxc)) hx

/-- Coverage over a class closed under contingent reasons excludes contingency there,
given factive reasons that discriminate every world where the explanandum fails and
well-founded contingent reasons. -/
theorem contrast_collapse (A : Arena W B F) (G : Plural W F) (a : W) (D : F → Prop)
    (hf : PFactive A G) (hc : PContrast A G) (hw : WellFoundedReasons A G a)
    (hcl : ClosedUnderReasons A G a D) (hcov : CoveredOn A G a D) :
    ∀ f, D f → ¬ Contingent A a f := by
  intro f
  induction f using hw.induction with
  | _ f ih =>
    intro hD hcf
    obtain ⟨Xs, hG⟩ := hcov f hD hcf
    obtain ⟨_, v, hv, hfv⟩ := hcf
    obtain ⟨x, hx, hxv⟩ := hc a Xs f hG v hv hfv
    have hxc : Contingent A a x := ⟨(hf a Xs f hG).1 x hx, v, hv, hxv⟩
    have hfc : Contingent A a f := ⟨(hf a Xs f hG).2, v, hv, hfv⟩
    exact ih x ⟨hxc, hfc, Xs, hG, hx⟩ (hcl f Xs x hD hG hx hxc) hxc

/-- The same from necessitation and bivalence. -/
theorem necessitating_collapse (A : Arena W B F) (G : Plural W F) (a : W) (D : F → Prop)
    (hf : PFactive A G) (hn : PNecessitating A G) (hb : Bivalent A)
    (hw : WellFoundedReasons A G a)
    (hcl : ClosedUnderReasons A G a D) (hcov : CoveredOn A G a D) :
    ∀ f, D f → ¬ Contingent A a f := by
  intro f
  induction f using hw.induction with
  | _ f ih =>
    intro hD hcf
    obtain ⟨Xs, hG⟩ := hcov f hD hcf
    obtain ⟨hfa, v, hv, hfv⟩ := hcf
    apply hfv
    apply hn a Xs f hG v hv
    intro x hx
    refine (hb v x).elim id fun hxv => False.elim ?_
    have hxc : Contingent A a x := ⟨(hf a Xs f hG).1 x hx, v, hv, hxv⟩
    exact ih x ⟨hxc, ⟨hfa, v, hv, hfv⟩, Xs, hG, hx⟩ (hcl f Xs x hD hG hx hxc) hxc

/-! ## Model lemmas -/

theorem wf_of_empty (A : Arena W B F) (G : Plural W F) (a : W)
    (h : ∀ e f, ¬ Below A G a e f) : WellFoundedReasons A G a :=
  ⟨fun f => ⟨f, fun e he => (h e f he).elim⟩⟩

theorem pair_contingent (f : PairFact) : Contingent pair false f :=
  ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩

theorem pair_sound : ConjunctSound pair := fun _ _ _ _ h => h

theorem pair_bccf : BCCFAt pair false .whole := ⟨rfl, fun _ _ => Or.inl rfl⟩

theorem brute_wf : WellFoundedReasons pair bruteMembers false := by
  have ha : ∀ e, ¬ Below pair bruteMembers false e .a := by
    rintro e ⟨_, _, _, ⟨_, h, _⟩, _⟩; cases h
  have hb : ∀ e, ¬ Below pair bruteMembers false e .b := by
    rintro e ⟨_, _, _, ⟨_, h, _⟩, _⟩; cases h
  refine ⟨fun f => ?_⟩
  have aa : Acc (Below pair bruteMembers false) .a := ⟨_, fun e he => (ha e he).elim⟩
  have ab : Acc (Below pair bruteMembers false) .b := ⟨_, fun e he => (hb e he).elim⟩
  have aw : Acc (Below pair bruteMembers false) .whole := by
    refine ⟨_, fun e he => ?_⟩
    obtain ⟨_, _, Xs, ⟨_, _, hX⟩, hx⟩ := he
    cases (hX e).1 hx with
    | inl h => exact h ▸ aa
    | inr h => exact h ▸ ab
  cases f <;> assumption

theorem not_acc_chain (x : Option Nat)
    (h : Acc (Below chain chainReasons none) x) : ∀ n, x = some n → False := by
  induction h with
  | intro x _ ih =>
    intro n hn
    subst hn
    have hm : ∀ k, Contingent chain none (some k) := fun k =>
      ⟨trivial, some 0, trivial, fun h => Nat.not_lt_zero k h⟩
    refine ih (some (n + 1)) ⟨hm _, hm _, (· = some (n + 1)), ⟨rfl, Or.inl ⟨n, rfl, fun _ => Iff.rfl⟩⟩, rfl⟩
      (n + 1) rfl

/-! ## The certificate -/

theorem derivativeReply : DerivativeReply := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W B F A G a t c hs hf hn hd hi hb ht hc hcov
    refine totality_collapse A G a (fun _ => True) t c hs hf hn
      (fun Xs g h hg => hd a Xs t g h hg) hi hb (fun _ _ _ _ _ _ _ => trivial)
      ⟨ht.1, fun q _ hq => ht.2 q hq⟩ trivial hc ?_
    have htc : Contingent A a t := by
      obtain ⟨hca, v, hv, hcv⟩ := hc
      exact ⟨ht.1, v, hv, fun h => hcv (hs c t v (ht.2 c ⟨hca, v, hv, hcv⟩) h)⟩
    exact hcov t trivial htc
  · intro W B F A G a D t c hs hf hn hd hi hb hcl ht hD hc hcov
    exact totality_collapse A G a D t c hs hf hn hd hi hb hcl ht hD hc hcov
  · intro W B F A G a D hf hn hb hw hcl hcov
    exact necessitating_collapse A G a D hf hn hb hw hcl hcov
  · intro W B F A G a D hf hc hw hcl hcov
    exact contrast_collapse A G a D hf hc hw hcl hcov
  · intro W B F A G hb hc w Xs f hG v hv hall
    refine (hb v f).elim id fun hfv => ?_
    obtain ⟨x, hx, hxv⟩ := hc w Xs f hG v hv hfv
    exact (hxv (hall x hx)).elim
  · intro W B F A
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro h w Xs f ⟨r, he, hX⟩
      exact ⟨fun x hx => ((hX x).1 hx) ▸ (h w r f he).1, (h w r f he).2⟩
    · rintro h w Xs f ⟨r, he, hX⟩ v hv hall
      exact h w r f he v hv (hall r ((hX r).2 rfl))
    · rintro h w Xs f g ⟨r, he, hX⟩ hg
      exact ⟨r, h w r f g he hg, hX⟩
    · rintro h w Xs e hc ⟨r, he, hX⟩ hx
      have hr := (hX e).1 hx
      subst hr
      exact h w e hc he
    · intro w f
      constructor
      · rintro ⟨r, he⟩
        exact ⟨(· = r), r, he, fun _ => Iff.rfl⟩
      · rintro ⟨_, r, he, _⟩
        exact ⟨r, he⟩
  -- bruteMembers
  · refine ⟨pair_sound, ?_, ?_, ?_, brute_wf, ?_, pair_bccf, pair_contingent _, ?_, ?_, ?_, ?_, ?_⟩
    · rintro w Xs f ⟨rfl, rfl, _⟩
      exact ⟨fun _ _ => rfl, rfl⟩
    · rintro w Xs f ⟨_, rfl, hX⟩ v _ hall
      exact hall .a ((hX .a).2 (Or.inl rfl))
    · rintro w Xs e _ ⟨_, rfl, hX⟩ hx
      cases (hX .whole).1 hx with
      | inl h => cases h
      | inr h => cases h
    · rintro f Xs x hf ⟨_, rfl, _⟩; exact (hf rfl).elim
    · exact ⟨fun x => x = .a ∨ x = .b, rfl, rfl, fun _ => Iff.rfl⟩
    · rintro ⟨Xs, _, h, _⟩; cases h
    · intro h
      have := h (fun x => x = .a ∨ x = .b) .a ⟨rfl, rfl, fun _ => Iff.rfl⟩ (Or.inl rfl)
      cases this.2.1
    · rintro f rfl _
      exact ⟨fun x => x = .a ∨ x = .b, rfl, rfl, fun _ => Iff.rfl⟩
    · intro h
      obtain ⟨Xs, _, hw, _⟩ := h .a (fun h => PairFact.noConfusion h) (pair_contingent _)
      cases hw
  -- loopMembers
  · refine ⟨pair_sound, ?_, ?_, ?_, pair_bccf, pair_contingent _,
      fun _ _ _ _ _ _ _ => trivial, ?_, ?_, ?_⟩
    · rintro w Xs f (⟨rfl, _, _⟩ | ⟨rfl, _⟩) <;> exact ⟨fun _ _ => rfl, rfl⟩
    · rintro w Xs f (⟨_, rfl, hX⟩ | ⟨_, (⟨rfl, hX⟩ | ⟨rfl, hX⟩)⟩) v _ hall
      · exact hall .a ((hX .a).2 (Or.inl rfl))
      · exact hall .b ((hX .b).2 rfl)
      · exact hall .a ((hX .a).2 rfl)
    · rintro w Xs e _ (⟨_, rfl, hX⟩ | ⟨_, (⟨rfl, hX⟩ | ⟨rfl, hX⟩)⟩) hx
      · cases (hX .whole).1 hx with
        | inl h => cases h
        | inr h => cases h
      · cases (hX .a).1 hx
      · cases (hX .b).1 hx
    · intro f _ _
      cases f
      · exact ⟨(· = .b), Or.inr ⟨rfl, Or.inl ⟨rfl, fun _ => Iff.rfl⟩⟩⟩
      · exact ⟨(· = .a), Or.inr ⟨rfl, Or.inr ⟨rfl, fun _ => Iff.rfl⟩⟩⟩
      · exact ⟨fun x => x = .a ∨ x = .b, Or.inl ⟨rfl, rfl, fun _ => Iff.rfl⟩⟩
    · intro h
      rcases h (fun x => x = .a ∨ x = .b) .a (Or.inl ⟨rfl, rfl, fun _ => Iff.rfl⟩) (Or.inl rfl) with
        ⟨_, hw, _⟩ | ⟨_, (⟨_, hX⟩ | ⟨hb, _⟩)⟩
      · cases hw
      · cases (hX .a).1 (Or.inl rfl)
      · cases hb
    · intro hw
      have hm : ∀ x : PairFact, Acc (Below pair loopMembers false) x → x ≠ .whole → False := by
        intro x hx
        induction hx with
        | intro x _ ih =>
          intro hne
          cases x with
          | a => exact ih .b ⟨pair_contingent _, pair_contingent _, (· = .b),
              Or.inr ⟨rfl, Or.inl ⟨rfl, fun _ => Iff.rfl⟩⟩, rfl⟩ (fun h => PairFact.noConfusion h)
          | b => exact ih .a ⟨pair_contingent _, pair_contingent _, (· = .a),
              Or.inr ⟨rfl, Or.inr ⟨rfl, fun _ => Iff.rfl⟩⟩, rfl⟩ (fun h => PairFact.noConfusion h)
          | whole => exact hne rfl
      exact hm .a (hw.apply _) (fun h => PairFact.noConfusion h)
  -- chain
  · have hm : ∀ k, Contingent chain none (some k) := fun k =>
      ⟨trivial, some 0, trivial, fun h => Nat.not_lt_zero k h⟩
    refine ⟨?_, ?_, ?_, ?_, ⟨rfl, fun _ _ => Or.inl rfl⟩, hm 0,
      fun _ _ _ _ _ _ _ => trivial, ?_, ?_, ?_, ?_⟩
    · rintro g f v (rfl | rfl) h
      · have hv : v = none := h
        subst hv
        cases g
        · exact rfl
        · exact trivial
      · exact h
    · rintro w Xs f ⟨rfl, (⟨n, rfl, hX⟩ | ⟨rfl, hX⟩)⟩
      · refine ⟨fun x hx => ?_, trivial⟩
        have := (hX x).1 hx
        subst this
        exact trivial
      · refine ⟨fun x hx => ?_, rfl⟩
        obtain ⟨n, hn⟩ := (hX x).1 hx
        subst hn
        exact trivial
    · rintro w Xs f ⟨_, (⟨n, rfl, hX⟩ | ⟨rfl, hX⟩)⟩ v _ hall
      · have h := hall (some (n + 1)) ((hX _).2 rfl)
        cases v with
        | none => exact trivial
        | some k => exact Nat.lt_of_succ_lt h
      · cases v with
        | none => exact rfl
        | some k =>
          exact (Nat.lt_irrefl k (hall (some k) ((hX _).2 ⟨k, rfl⟩))).elim
    · rintro w Xs e _ ⟨_, (⟨n, rfl, hX⟩ | ⟨rfl, hX⟩)⟩ hx
      · have := (hX (some n)).1 hx
        injection this with h
        exact Nat.succ_ne_self n h.symm
      · obtain ⟨n, hn⟩ := (hX none).1 hx
        cases hn
    · intro f _ _
      cases f with
      | none => exact ⟨_, rfl, Or.inr ⟨rfl, fun _ => Iff.rfl⟩⟩
      | some n => exact ⟨_, rfl, Or.inl ⟨n, rfl, fun _ => Iff.rfl⟩⟩
    · intro h
      obtain ⟨_, (⟨n, hn, hX⟩ | ⟨hh, _⟩)⟩ := h (fun x => ∃ n, x = some n) (some 0)
        ⟨rfl, Or.inr ⟨rfl, fun _ => Iff.rfl⟩⟩ (Or.inl rfl)
      · injection hn with h0
        subst h0
        have := (hX (some 0)).1 ⟨0, rfl⟩
        injection this with h1
        cases h1
      · cases hh
    · exact fun hw => not_acc_chain (some 0) (hw.apply _) 0 rfl
    · rintro e ⟨_, _, Xs, ⟨_, (⟨n, rfl, hX⟩ | ⟨rfl, hX⟩)⟩, hx⟩
      · have := (hX (some n)).1 hx
        injection this with h
        exact Nat.succ_ne_self n h.symm
      · obtain ⟨n, hn⟩ := (hX none).1 hx
        cases hn
  -- ground true
  · have hg : ∀ {w r f}, (ground true).explains w r f →
        r = .ground ∧ (f = .ground ∨ (f = .choice ∧ w = false)) := by
      intro w r f h
      cases r <;> cases f
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr ⟨rfl, h⟩⟩
      · exact h.elim
      · exact h.elim
    have hnc : ∀ w, ¬ Contingent (ground true) w .ground := fun _ ⟨_, _, _, h⟩ => h trivial
    have hwit : ofSingle (ground true) false (· = .ground) .choice :=
      ⟨.ground, rfl, fun _ => Iff.rfl⟩
    refine ⟨fun _ => trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ _ _ _ _ _ _ => trivial, ?_, ?_, ?_⟩
    · rintro g f v rfl h; exact h
    · rintro w Xs f ⟨r, he, hX⟩
      obtain ⟨rfl, hf⟩ := hg he
      refine ⟨fun x hx => ?_, ?_⟩
      · have := (hX x).1 hx
        subst this
        exact trivial
      · rcases hf with rfl | ⟨rfl, rfl⟩
        · exact trivial
        · exact rfl
    · rintro w Xs f g h rfl; exact h
    · rintro w Xs e hc ⟨r, he, hX⟩ hx
      obtain ⟨rfl, _⟩ := hg he
      have := (hX e).1 hx
      subst this
      exact hnc w hc
    · refine wf_of_empty _ _ _ ?_
      rintro e f ⟨hc, _, Xs, ⟨r, he, hX⟩, hx⟩
      obtain ⟨rfl, _⟩ := hg he
      have := (hX e).1 hx
      subst this
      exact hnc _ hc
    · refine ⟨rfl, fun q hq => ?_⟩
      cases q
      · exact (hnc _ hq).elim
      · exact rfl
    · exact ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩
    · intro f _ _
      cases f
      · exact ⟨(· = .ground), .ground, rfl, fun _ => Iff.rfl⟩
      · exact ⟨_, hwit⟩
    · intro h
      exact Bool.noConfusion (h false _ .choice hwit true trivial (fun x hx => by
        subst hx; exact trivial))
    · intro h
      obtain ⟨x, hx, hxv⟩ := h false _ .choice hwit true trivial (fun h => Bool.noConfusion h)
      subst hx
      exact hxv trivial
  -- scopeOnly
  · refine ⟨pair_sound, ?_, ?_, ?_, ?_, pair_bccf, pair_contingent _, ?_, ?_, ?_⟩
    · rintro w Xs f ⟨rfl, _⟩; exact ⟨fun _ _ => rfl, rfl⟩
    · rintro w Xs f ⟨_, (⟨rfl, hX⟩ | ⟨rfl, hX⟩)⟩ v _ hall
      · exact hall .b ((hX .b).2 rfl)
      · exact hall .a ((hX .a).2 rfl)
    · rintro w Xs f g ⟨h0, (⟨rfl, hX⟩ | ⟨rfl, hX⟩)⟩ (h | rfl)
      · cases h
      · exact ⟨h0, Or.inl ⟨rfl, hX⟩⟩
      · cases h
      · exact ⟨h0, Or.inr ⟨rfl, hX⟩⟩
    · rintro w Xs e _ ⟨_, (⟨rfl, hX⟩ | ⟨rfl, hX⟩)⟩ hx
      · cases (hX .a).1 hx
      · cases (hX .b).1 hx
    · rintro f Xs x _ ⟨_, (⟨rfl, hX⟩ | ⟨rfl, hX⟩)⟩ hx _
      · have h := (hX x).1 hx
        subst h
        exact fun h => PairFact.noConfusion h
      · have h := (hX x).1 hx
        subst h
        exact fun h => PairFact.noConfusion h
    · intro f hf _
      cases f
      · exact ⟨(· = .b), rfl, Or.inl ⟨rfl, fun _ => Iff.rfl⟩⟩
      · exact ⟨(· = .a), rfl, Or.inr ⟨rfl, fun _ => Iff.rfl⟩⟩
      · exact (hf rfl).elim
    · rintro ⟨Xs, _, (⟨h, _⟩ | ⟨h, _⟩)⟩ <;> cases h
  -- pairOutside
  · have hc : ∀ f, Contingent pairOutside false f := fun _ =>
      ⟨rfl, true, trivial, fun h => Bool.noConfusion h⟩
    refine ⟨fun _ _ _ _ h => h, ?_, ?_, ?_, ?_, ?_, ?_, hc _, ?_, ?_, ?_⟩
    · rintro w Xs f ⟨rfl, _⟩; exact ⟨fun _ _ => rfl, rfl⟩
    · rintro w Xs f ⟨_, _, hX⟩ v _ hall
      exact hall .b ((hX .b).2 rfl)
    · rintro Xs g h (⟨rfl, _⟩ | rfl)
      · exact ⟨rfl, Or.inl rfl, h.2.2⟩
      · exact h
    · rintro w Xs e _ ⟨_, (rfl | rfl), hX⟩ hx
      · cases (hX .a).1 hx
      · cases (hX .whole).1 hx
    · refine ⟨fun f => ?_⟩
      have ab : Acc (Below pairOutside outsideReason false) .b := ⟨_, fun e he => by
        obtain ⟨_, _, _, ⟨_, h, _⟩, _⟩ := he
        cases h with
        | inl h => cases h
        | inr h => cases h⟩
      have rest : ∀ f, Acc (Below pairOutside outsideReason false) f := by
        intro f
        refine ⟨_, fun e he => ?_⟩
        obtain ⟨_, _, Xs, ⟨_, _, hX⟩, hx⟩ := he
        exact ((hX e).1 hx) ▸ ab
      exact rest f
    · exact ⟨rfl, fun q hq _ => Or.inl ⟨hq, rfl⟩⟩
    · rintro f rfl _
      exact ⟨(· = .b), rfl, Or.inl rfl, fun _ => Iff.rfl⟩
    · exact ⟨(· = .b), rfl, Or.inr rfl, fun _ => Iff.rfl⟩
    · intro h
      cases h .a (· = .b) .b rfl ⟨rfl, Or.inl rfl, fun _ => Iff.rfl⟩ rfl (hc _)
  -- pairToken
  · have hb : ∀ w, ¬ pairToken.holds w .b := fun _ h => h.2 rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro g f v (⟨rfl, rfl⟩ | rfl) h
      · exact ⟨h.1, fun h => PairFact.noConfusion h⟩
      · exact h
    · rintro w Xs f ⟨_, _, hX⟩ v _ hall
      exact (hb v (hall .b ((hX .b).2 rfl))).elim
    · refine wf_of_empty _ _ _ ?_
      rintro e f ⟨hc, _, Xs, ⟨_, _, hX⟩, hx⟩
      have := (hX e).1 hx
      subst this
      exact hb _ hc.1
    · rintro f Xs x _ ⟨_, _, hX⟩ hx hc
      have := (hX x).1 hx
      subst this
      exact (hb _ hc.1).elim
    · exact ⟨⟨rfl, fun h => PairFact.noConfusion h⟩, true, trivial, fun h => Bool.noConfusion h.1⟩
    · rintro f rfl _
      exact ⟨(· = .b), rfl, Or.inl rfl, fun _ => Iff.rfl⟩
    · intro h
      exact hb _ ((h false (· = .b) .a ⟨rfl, Or.inl rfl, fun _ => Iff.rfl⟩).1 .b rfl)
  -- pairNecessary
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ _ h => h.elim
    · exact fun _ _ _ h => h.elim
    · refine wf_of_empty _ _ _ ?_
      rintro _ _ ⟨_, _, _, h, _⟩; exact h
    · exact fun _ _ _ _ _ _ _ => trivial
    · exact fun _ _ ⟨_, _, _, h⟩ => (h trivial).elim
    · exact fun _ ⟨_, _, _, h⟩ => h trivial
  -- bivalence
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun v _ => Decidable.em (v = false)
    · intro v f
      cases f with
      | none => exact Decidable.em (v = none)
      | some n =>
        cases v with
        | none => exact Or.inl trivial
        | some k => exact Decidable.em (n < k)
    · intro v f
      cases f
      · exact Or.inl trivial
      · exact Decidable.em (v = false)
    · exact fun v _ => Decidable.em (v = false)
    · intro v f
      cases f
      · exact (Decidable.em (v = false)).elim (fun h => Or.inl ⟨h, fun h => PairFact.noConfusion h⟩)
          (fun h => Or.inr fun h' => h h'.1)
      · exact Or.inr fun h => h.2 rfl
      · exact (Decidable.em (v = false)).elim (fun h => Or.inl ⟨h, fun h => PairFact.noConfusion h⟩)
          (fun h => Or.inr fun h' => h h'.1)
    · exact fun _ _ => Or.inl trivial

end TruthCore.Results.Explanation.BCCFDerivative
