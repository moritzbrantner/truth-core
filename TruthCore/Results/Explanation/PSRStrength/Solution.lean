import TruthCore.Explanation.PSRStrength

namespace TruthCore.Results.Explanation.PSRStrength
open TruthCore.Explanation.PSRStrength
open TruthCore.German.Kant.CosmologicalInference

variable {W B F : Type}

/-! ## The general lemmas -/

/-- A true necessitating reason for a contingent fact is itself contingent: at the
world where the explanandum fails, the reason fails too. No case split on whether
the reason is necessary is needed. -/
theorem necessitating_reason_contingent (A : Arena W B F) (hn : Necessitating A)
    {w : W} {r f : F} (he : A.explains w r f) (hr : A.holds w r)
    (hc : Contingent A w f) : Contingent A w r := by
  obtain ⟨_, v, hv, hf⟩ := hc
  exact ⟨hr, v, hv, fun hrv => hf (hn w r f he v hv hrv)⟩

/-- The aggregate of all contingent truths is itself contingent as soon as one
contingent truth exists. -/
theorem bccf_contingent (A : Arena W B F) (hs : ConjunctSound A) {a : W} {t c : F}
    (ht : BCCFAt A a t) (hc : Contingent A a c) : Contingent A a t := by
  obtain ⟨hca, v, hv, hcv⟩ := hc
  exact ⟨ht.1, v, hv, fun htv => hcv (hs c t v (ht.2 c ⟨hca, v, hv, hcv⟩) htv)⟩

/-- The collapse through distribution and contingent irreflexivity. -/
theorem collapse_distribution (A : Arena W B F) (a : W) (t c : F)
    (hs : ConjunctSound A) (hf : Factive A) (hn : Necessitating A) (hd : Distribution A)
    (hi : IrreflexiveContingent A) (ht : BCCFAt A a t) (hc : Contingent A a c)
    (hb : NoBrute A a) : False := by
  have htc := bccf_contingent A hs ht hc
  refine hb ⟨t, htc, ?_⟩
  intro ⟨r, he⟩
  have hrc := necessitating_reason_contingent A hn he (hf a r t he).1 htc
  exact hi a r hrc (hd a r t r he (ht.2 r hrc))

/-- The collapse through independence of the reason from its target. -/
theorem collapse_independent (A : Arena W B F) (a : W) (t c : F)
    (hs : ConjunctSound A) (hf : Factive A) (hn : Necessitating A)
    (hi : ReasonIndependent A) (ht : BCCFAt A a t) (hc : Contingent A a c)
    (hb : NoBrute A a) : False := by
  have htc := bccf_contingent A hs ht hc
  refine hb ⟨t, htc, ?_⟩
  intro ⟨r, he⟩
  have hrc := necessitating_reason_contingent A hn he (hf a r t he).1 htc
  exact hi a r t he htc fun v hv =>
    ⟨fun hrv => hn a r t he v hv hrv, fun htv => hs r t v (ht.2 r hrc) htv⟩

/-- Weak PSR gives `NoBrute` through distribution and the diagonal facts. -/
theorem weak_noBrute (A : Arena W B F) (a : W) (hd : Distribution A)
    (hu : UnexplainedFacts A a) (hw : WeakPSR A a) : NoBrute A a := by
  intro ⟨f, ⟨hfa, v, hv, hfv⟩, hne⟩
  obtain ⟨u, hc, hiff⟩ := hu f ⟨hfa, v, hv, hfv⟩ hne
  have huc : Contingent A a u :=
    ⟨(hiff a).2 ⟨hfa, hne⟩, v, hv, fun huv => hfv ((hiff v).1 huv).1⟩
  obtain ⟨x, _, hux, r, he⟩ := hw u huc
  exact ((hiff x).1 hux).2 ⟨r, hd x r u f he hc⟩

/-- Extensional domains supply both bridges. -/
theorem extensional_bridges (A : Arena W B F) (a : W) (he : Extensional A)
    (hc : EntailmentConjunct A) : UnexplainedFacts A a ∧ ∃ t, BCCFAt A a t := by
  constructor
  · intro f _ _
    obtain ⟨u, hu⟩ := he fun v => A.holds v f ∧ ¬ Explained A v f
    exact ⟨u, (hc f u).2 fun v hv => ((hu v).1 hv).1, hu⟩
  · obtain ⟨t, ht⟩ := he fun v => ∀ q, Contingent A a q → A.holds v q
    exact ⟨t, (ht a).2 fun q hq => hq.1, fun q hq => (hc q t).2 fun v hv => (ht v).1 hv q hq⟩

/-- In an extensional domain, weak PSR with a factive, necessitating, distributing,
irreflexive reason relation excludes all contingency at `a`. -/
theorem extensional_weak_collapse (A : Arena W B F) (a : W) (he : Extensional A)
    (hc : EntailmentConjunct A) (hf : Factive A) (hn : Necessitating A)
    (hd : Distribution A) (hi : IrreflexiveContingent A) (hw : WeakPSR A a) (c : F) :
    ¬ Contingent A a c := by
  intro hcc
  obtain ⟨hu, t, ht⟩ := extensional_bridges A a he hc
  exact collapse_distribution A a t c (fun g f v hg hfv => (hc g f).1 hg v hfv) hf hn hd hi
    ht hcc (weak_noBrute A a hd hu hw)

/-! ## Elementary helpers -/

private theorem tf : (true : Bool) = false → False := fun h => Bool.noConfusion h
private theorem ft : (false : Bool) = true → False := fun h => Bool.noConfusion h

/-- Every list of naturals has a strict upper bound. -/
private theorem exists_bound : ∀ l : List Nat, ∃ b, ∀ y, y ∈ l → y < b
  | [] => ⟨0, fun _ h => nomatch h⟩
  | a :: l => by
    obtain ⟨b, hb⟩ := exists_bound l
    refine ⟨a + 1 + b, fun y hy => ?_⟩
    cases hy with
    | head => exact Nat.lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.le_add_right (a + 1) b)
    | tail _ h => exact Nat.lt_of_lt_of_le (hb y h) (Nat.le_add_left b (a + 1))

private theorem exists_fresh (l : List Nat) : ∃ x, x ∉ l := by
  obtain ⟨b, hb⟩ := exists_bound l
  exact ⟨b, fun h => Nat.lt_irrefl b (hb b h)⟩

/-! ## The brute terminus -/

private theorem terminus_factive : Factive bruteTerminus := by
  intro w r f h
  cases r <;> cases f <;> first | exact False.elim h | exact ⟨h, h⟩

private theorem terminus_distribution : Distribution bruteTerminus := by
  intro w r f g h hc
  cases r <;> cases f <;> cases g <;>
    first | exact False.elim h | exact False.elim hc | exact h

private theorem terminus_irreflexive : IrreflexiveContingent bruteTerminus := by
  intro w r _ h
  cases r <;> exact h

/-! ## The false reason token -/

private theorem falseToken_necessitating : Necessitating falseToken := by
  intro w r f h v _ hr
  have hrf : r = false := h.1
  subst hrf
  exact (ft hr.1).elim

private theorem falseToken_contingent_true {w : Bool} {f : Bool}
    (h : Contingent falseToken w f) : f = true := h.1.1

/-! ## The nonnecessitating ground -/

private theorem ground_contingent {s : Bool} {w : Bool} {f : GroundFact}
    (h : Contingent (ground s) w f) : f = .choice := by
  cases f with
  | choice => rfl
  | ground =>
    obtain ⟨_, _, _, hn⟩ := h
    exact (hn True.intro).elim

private theorem ground_not_necessitating : ¬ Necessitating (ground true) := fun h =>
  tf (h false .ground .choice rfl true True.intro True.intro)

private theorem ground_factive (s : Bool) : Factive (ground s) := by
  intro w r f h
  cases r <;> cases f
  · exact ⟨True.intro, True.intro⟩
  · exact ⟨True.intro, h⟩
  · exact False.elim h
  · exact False.elim h

private theorem ground_contingent_choice (s : Bool) :
    Contingent (ground s) false .choice := ⟨rfl, true, True.intro, tf⟩

private theorem ground_true_noBrute : NoBrute (ground true) false := by
  intro ⟨f, hc, hne⟩
  have hf := ground_contingent hc
  subst hf
  exact hne ⟨.ground, rfl⟩

private theorem ground_irreflexive (s : Bool) : IrreflexiveContingent (ground s) := by
  intro w r hc h
  have hr := ground_contingent hc
  subst hr
  exact h

private theorem ground_contingentPSR_false (s : Bool) (w : Bool) :
    ContingentPSR (ground s) w := by
  intro f hc
  have hf := ground_contingent hc
  subst hf
  exact ⟨.ground, hc.1⟩

private theorem ground_conjunct_sound (s : Bool) : ConjunctSound (ground s) := by
  intro g f v hc hf
  have hgf : g = f := hc
  subst hgf
  exact hf

private theorem ground_distribution (s : Bool) : Distribution (ground s) := by
  intro w r f g h hc
  have hgf : g = f := hc
  subst hgf
  exact h

private theorem ground_coherent (s : Bool) : Coherent (ground s) := by
  intro w x
  cases x <;> exact Iff.rfl

private theorem ground_independent : ReasonIndependent (ground true) := by
  intro w r f h hc hco
  have hf := ground_contingent hc
  subst hf
  cases r with
  | choice => exact h
  | ground => exact tf ((hco true True.intro).1 True.intro)

/-! ## The cofinite domain -/

private theorem cofinite_sound : ConjunctSound cofinite :=
  fun _ _ _ hc hf hg => hf (hc _ hg)

private theorem cofinite_factive : Factive cofinite :=
  fun _ _ _ h => ⟨h.1, fun hf => h.1 (h.2.1 _ hf)⟩

private theorem cofinite_necessitating : Necessitating cofinite :=
  fun _ _ _ h _ _ hr hf => hr (h.2.1 _ hf)

private theorem cofinite_distribution : Distribution cofinite := by
  intro _ _ _ _ ⟨hw, hs, x, hx, hxf⟩ hc
  exact ⟨hw, fun y hy => hs y (hc y hy), x, hx, fun hg => hxf (hc x hg)⟩

private theorem cofinite_irreflexive : IrreflexiveContingent cofinite := by
  intro _ _ _ ⟨_, _, x, hx, hnx⟩
  exact hnx hx

private theorem cofinite_contingent (a x : Nat) (hx : x ≠ a) :
    Contingent cofinite a [x] := by
  refine ⟨?_, x, True.intro, fun h => h (List.Mem.head _)⟩
  intro h
  cases h with
  | head => exact hx rfl
  | tail _ h => exact nomatch h

private theorem cofinite_no_bccf (a : Nat) (t : List Nat) : ¬ BCCFAt cofinite a t := by
  intro h
  obtain ⟨x, hx⟩ := exists_fresh (a :: t)
  have hne : x ≠ a := fun e => hx (e ▸ List.Mem.head _)
  exact hx (List.Mem.tail _ (h.2 [x] (cofinite_contingent a x hne) x (List.Mem.head _)))

private theorem cofinite_some_contingent (a : Nat) : ∃ c, Contingent cofinite a c :=
  ⟨[a + 1], cofinite_contingent a (a + 1) (Nat.succ_ne_self a)⟩

private theorem cofinite_factPSR (a : Nat) : FactPSR cofinite a := by
  intro f hf
  obtain ⟨x, hx⟩ := exists_fresh (a :: f)
  refine ⟨x :: f, ?_, fun y hy => List.Mem.tail _ hy, x, List.Mem.head _,
    fun h => hx (List.Mem.tail _ h)⟩
  intro h
  cases h with
  | head => exact hx (List.Mem.head _)
  | tail _ h => exact hf h

private theorem cofinite_noBrute (a : Nat) : NoBrute cofinite a := by
  intro ⟨f, hc, hne⟩
  exact hne (cofinite_factPSR a f hc.1)

private theorem cofinite_independent : ReasonIndependent cofinite := by
  intro _ _ _ ⟨_, _, x, hx, hxf⟩ _ h
  exact (h x True.intro).2 hxf hx

private theorem append_left (l r : List Nat) (y : Nat) (h : y ∈ l) : y ∈ l ++ r := by
  induction l with
  | nil => exact nomatch h
  | cons a l ih =>
    cases h with
    | head => exact List.Mem.head _
    | tail _ h => exact List.Mem.tail _ (ih h)

private theorem append_right (l r : List Nat) (y : Nat) (h : y ∈ r) : y ∈ l ++ r := by
  induction l with
  | nil => exact h
  | cons a l ih => exact List.Mem.tail _ ih

private theorem append_cases (l r : List Nat) (y : Nat) (h : y ∈ l ++ r) : y ∈ l ∨ y ∈ r := by
  induction l with
  | nil => exact Or.inr h
  | cons a l ih =>
    cases h with
    | head => exact Or.inl (List.Mem.head _)
    | tail _ h =>
      cases ih h with
      | inl h => exact Or.inl (List.Mem.tail _ h)
      | inr h => exact Or.inr h

private theorem cofinite_closure (l r : List Nat) :
    ∃ j, cofinite.conjunct l j ∧ cofinite.conjunct r j ∧
      ∀ v, cofinite.holds v j ↔ (cofinite.holds v l ∧ cofinite.holds v r) := by
  refine ⟨l ++ r, append_left l r, append_right l r, fun v => ⟨?_, ?_⟩⟩
  · exact fun h => ⟨fun hl => h (append_left l r v hl), fun hr => h (append_right l r v hr)⟩
  · exact fun h hj => (append_cases l r v hj).elim h.1 h.2

/-! ## Mutual reasons and the small quality controls -/

private theorem mutual_not_distribution : ¬ Distribution mutualReasons := fun h =>
  (h false false true false ⟨rfl, ft⟩ (Or.inl rfl)).2 rfl

private theorem mutual_noBrute : NoBrute mutualReasons false := by
  intro ⟨f, _, hne⟩
  cases f
  · exact hne ⟨true, rfl, tf⟩
  · exact hne ⟨false, rfl, ft⟩

private theorem allNecessary_not_contingent (w : Bool) (c : Bool) :
    ¬ Contingent allNecessary w c := fun ⟨_, _, _, h⟩ => h True.intro

/-! ## The infinite history -/

private theorem history_sound (b : Bool) : ConjunctSound (history b) := by
  intro g f v hc hf
  cases g <;> cases f <;> cases v <;>
    first
    | exact False.elim hc
    | exact False.elim hf
    | exact True.intro
    | exact hf
    | (cases hc; exact hf)

private theorem history_factive (b : Bool) : Factive (history b) := by
  intro w r f ⟨hw, hl⟩
  cases hw
  cases r <;> cases f <;>
    first | exact False.elim hl | exact ⟨True.intro, True.intro⟩

private theorem history_necessitating (b : Bool) : Necessitating (history b) := by
  intro w r f ⟨hw, hl⟩ v _ hr
  cases hw
  cases r <;> cases f
  case member.member m n =>
    have hm : m = n + 1 := hl
    subst hm
    cases v with
    | lawful => exact True.intro
    | rogue => exact True.intro
    | cut k => exact Nat.lt_of_succ_lt hr
  all_goals first
    | exact False.elim hl
    | (cases v <;> first | exact True.intro | exact False.elim hr)

private theorem history_independent (b : Bool) : ReasonIndependent (history b) := by
  intro w r f ⟨hw, hl⟩ hcon h
  cases hw
  cases r <;> cases f
  case member.member m n =>
    have hm : m = n + 1 := hl
    subst hm
    exact Nat.lt_irrefl (n + 1) ((h (.cut (n + 1)) True.intro).2 (Nat.lt_succ_self n))
  all_goals first
    | exact False.elim hl
    | exact (h .rogue True.intro).2 True.intro

private theorem history_distribution (b : Bool) : Distribution (history b) := by
  intro w r f g ⟨hw, hl⟩ hc
  refine ⟨hw, ?_⟩
  cases r <;> cases f <;> cases g <;>
    first
    | exact False.elim hl
    | exact False.elim hc
    | exact hl
    | (cases hc; exact hl)

private theorem history_irreflexive (b : Bool) : IrreflexiveContingent (history b) := by
  intro w r _ ⟨_, hl⟩
  cases r with
  | member m => exact Nat.succ_ne_self m (Eq.symm hl)
  | hist => exact hl
  | law => exact hl

private theorem history_not_explained_law (b : Bool) :
    ¬ Explained (history b) .lawful .law := by
  intro ⟨r, _, hl⟩
  cases r <;> exact hl

private theorem history_law_contingent (b : Bool) :
    Contingent (history b) .lawful .law := ⟨True.intro, .rogue, True.intro, id⟩

private theorem history_bundle (b : Bool) :
    ConjunctSound (history b) ∧ Factive (history b) ∧ Necessitating (history b) ∧
    ReasonIndependent (history b) ∧ Distribution (history b) ∧
    IrreflexiveContingent (history b) ∧
    BCCFAt (history b) .lawful .law ∧
    Contingent (history b) .lawful .hist ∧ Contingent (history b) .lawful .law ∧
    (∀ n, Explained (history b) .lawful (.member n)) ∧
    ¬ Explained (history b) .lawful .law ∧
    ¬ CommonReason (history b) .lawful :=
  ⟨history_sound b, history_factive b, history_necessitating b, history_independent b,
    history_distribution b, history_irreflexive b,
    ⟨True.intro, fun q _ => by cases q <;> exact True.intro⟩,
    ⟨True.intro, .cut 0, True.intro, id⟩, history_law_contingent b,
    fun n => ⟨.member (n + 1), rfl, rfl⟩, history_not_explained_law b,
    fun ⟨r, h⟩ => history_not_explained_law b ⟨r, h _ (history_law_contingent b)⟩⟩

private theorem history_false_hist_unexplained :
    ¬ Explained (history false) .lawful .hist := by
  intro ⟨r, _, hl⟩
  cases r with
  | member _ => exact hl
  | hist => exact hl
  | law => exact ft hl

/-! ## The modal models -/

private theorem modalGap_contingent {w : Option Bool} {f : Bool}
    (h : Contingent modalGap w f) : f = true := by
  cases f with
  | true => rfl
  | false =>
    obtain ⟨_, _, _, hn⟩ := h
    exact (hn (Or.inl rfl)).elim

private theorem some_ne_none (b : Bool) : (some b : Option Bool) ≠ none :=
  fun h => by cases h

private theorem modalGap_fact_contingent (b : Bool) :
    Contingent modalGap (some b) true :=
  ⟨Or.inr (some_ne_none b), none, True.intro, fun h => by
    cases h with
    | inl h => exact tf h
    | inr h => exact h rfl⟩

private theorem modalGap_unexplained_false : ¬ Explained modalGap (some false) true := by
  intro ⟨_, h, _⟩
  exact ft (Option.some.inj h)

private theorem modalGap_no_diagonal : ¬ UnexplainedFacts modalGap (some false) := by
  intro h
  obtain ⟨u, hc, hiff⟩ := h true (modalGap_fact_contingent false) modalGap_unexplained_false
  have hu : true = u := hc
  subst hu
  exact ((hiff (some true)).1 (Or.inr (some_ne_none true))).2 ⟨false, rfl, rfl, rfl⟩

private theorem modalGap_factive : Factive modalGap := by
  intro w r f ⟨hw, hr, _⟩
  subst hw
  exact ⟨Or.inl hr, Or.inr (some_ne_none true)⟩

private theorem modalGap_distribution : Distribution modalGap := by
  intro w r f g h hc
  have hgf : g = f := hc
  subst hgf
  exact h

private theorem modalGap_weak : WeakPSR modalGap (some false) := by
  intro f hc
  have hf := modalGap_contingent hc
  subst hf
  exact ⟨some true, True.intro, Or.inr (some_ne_none true), false, rfl, rfl, rfl⟩

private theorem modalGap_contingentPSR_true : ContingentPSR modalGap (some true) := by
  intro f hc
  have hf := modalGap_contingent hc
  subst hf
  exact ⟨false, rfl, rfl, rfl⟩

private theorem diagonal_necessary_not_contingent {w : Option Bool} :
    ¬ Contingent modalGapDiagonal w .necessary := fun ⟨_, _, _, h⟩ => h True.intro

private theorem diagonal_factive : Factive modalGapDiagonal := by
  intro w r f ⟨hr, hf⟩
  cases f with
  | necessary => exact False.elim hf
  | fact =>
    have hw : w = some true := hf
    subst hw
    subst hr
    exact ⟨True.intro, some_ne_none true⟩
  | unexplained =>
    subst hr
    exact ⟨True.intro, hf⟩

private theorem diagonal_explained_fact (v : Option Bool) :
    Explained modalGapDiagonal v .fact → v = some true := fun ⟨_, _, h⟩ => h

private theorem diagonal_fact_contingent :
    Contingent modalGapDiagonal (some false) .fact :=
  ⟨some_ne_none false, none, True.intro, fun h => h rfl⟩

private theorem diagonal_unexplained_fact :
    ¬ Explained modalGapDiagonal (some false) .fact := fun h =>
  ft (Option.some.inj (diagonal_explained_fact _ h))

private theorem diagonal_bridge : UnexplainedFacts modalGapDiagonal (some false) := by
  intro f hc hne
  cases f with
  | necessary => exact (diagonal_necessary_not_contingent hc).elim
  | unexplained => exact (hne ⟨.necessary, rfl, rfl⟩).elim
  | fact =>
    refine ⟨.unexplained, True.intro, fun v => ⟨?_, ?_⟩⟩
    · intro h
      have hv : v = some false := h
      subst hv
      exact ⟨some_ne_none false, diagonal_unexplained_fact⟩
    · intro ⟨h1, h2⟩
      match v, h1, h2 with
      | none, h1, _ => exact (h1 rfl).elim
      | some true, _, h2 => exact (h2 ⟨.necessary, rfl, rfl⟩).elim
      | some false, _, _ => exact rfl

private theorem diagonal_not_distribution : ¬ Distribution modalGapDiagonal := fun h =>
  diagonal_unexplained_fact
    ⟨.necessary, h (some false) .necessary .unexplained .fact ⟨rfl, rfl⟩ True.intro⟩

private theorem diagonal_weak : WeakPSR modalGapDiagonal (some false) := by
  intro f hc
  cases f with
  | necessary => exact (diagonal_necessary_not_contingent hc).elim
  | fact => exact ⟨some true, True.intro, some_ne_none true, .necessary, rfl, rfl⟩
  | unexplained => exact ⟨some false, True.intro, rfl, .necessary, rfl, rfl⟩

private theorem nonReflexive_contingent {w f : Bool}
    (h : Contingent nonReflexive w f) : f = true := by
  cases f with
  | true => rfl
  | false =>
    obtain ⟨_, _, _, hn⟩ := h
    exact (hn (Or.inl rfl)).elim

private theorem nonReflexiveBare_false :
    ¬ nonReflexiveBare.holds true true := by
  intro h
  cases h with
  | inl h => exact tf h
  | inr h => exact tf h

private theorem nonReflexiveBare_necessary : NecessaryPSR nonReflexiveBare false := by
  intro v hv f hc
  have hvt : v = true := hv
  subst hvt
  cases f with
  | true => exact (nonReflexiveBare_false hc.1).elim
  | false =>
    obtain ⟨_, _, _, hn⟩ := hc
    exact (hn (Or.inl rfl)).elim

private theorem shifting_not_stable (f : Bool) : ¬ StableReason shiftingReason f := by
  intro ⟨r, h⟩
  have h1 : r = true := h true True.intro
  have h2 : r = false := h false True.intro
  exact tf (h1.symm.trans h2)

/-! ## Existence-only, cause-only and extensional controls -/

private theorem existenceOnly_factive : Factive existenceOnly := by
  intro w r f h
  cases r <;> cases f <;> first | exact False.elim h | exact ⟨True.intro, True.intro⟩

private theorem existenceOnly_unexplained (w : Bool) : ¬ Explained existenceOnly w .event := by
  intro ⟨r, h⟩
  cases r <;> exact h

private theorem extensionalGround_bundle :
    Extensional extensionalGround ∧ EntailmentConjunct extensionalGround ∧
    Factive extensionalGround ∧ ¬ Necessitating extensionalGround ∧
    Distribution extensionalGround ∧ IrreflexiveContingent extensionalGround ∧
    FactPSR extensionalGround false ∧
    (∃ c, Contingent extensionalGround false c) ∧ (∃ t, BCCFAt extensionalGround false t) := by
  have hex : Extensional extensionalGround := fun P => ⟨P, fun _ => Iff.rfl⟩
  have hen : EntailmentConjunct extensionalGround := fun _ _ => Iff.rfl
  refine ⟨hex, hen, ?_, ?_, ?_, ?_, ?_, ?_, (extensional_bridges _ false hex hen).2⟩
  · exact fun _ _ _ h => ⟨h.1 _, h.2⟩
  · intro h
    have : (true : Bool) = false :=
      h false (fun _ => True) (fun w => w = false) ⟨fun _ => True.intro, rfl⟩ true
        True.intro True.intro
    exact tf this
  · exact fun _ _ _ _ h hc => ⟨h.1, hc _ h.2⟩
  · exact fun _ _ ⟨_, _, _, hn⟩ h => hn (h.1 _)
  · exact fun _ hf => ⟨fun _ => True, fun _ => True.intro, hf⟩
  · exact ⟨fun w => w = false, rfl, true, True.intro, tf⟩

/-! ## The embedding of #312 -/

private theorem ofModel_explained {E : Type} (m : TruthCore.Explanation.ExistencePSR.Model W E)
    (w : W) (x : E) :
    Explained (ofModel m) w ((ofModel m).exist x) ↔ ∃ r, m.explains w r (.fact x) := by
  constructor
  · intro ⟨r, h⟩
    cases r with
    | inl _ => exact False.elim h
    | inr r => exact ⟨r, h⟩
  · intro ⟨r, h⟩
    exact ⟨.inr r, h⟩

/-! ## The certificates -/

theorem collapseCore : CollapseCore := by
  refine ⟨fun W B F A a t c => ?_, fun W B F A a t c => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun hs hf hn hd hi ht hc hb => collapse_distribution A a t c hs hf hn hd hi ht hc hb
  · exact fun hs hf hn hi ht hc hb => collapse_independent A a t c hs hf hn hi ht hc hb
  · exact ⟨fun _ _ _ _ h => h, terminus_factive, fun _ _ _ _ _ _ h => h,
      terminus_distribution, terminus_irreflexive,
      ⟨rfl, fun q _ => by cases q <;> exact True.intro⟩, ⟨rfl, true, True.intro, tf⟩,
      fun h => h ⟨.terminus, ⟨rfl, true, True.intro, tf⟩, fun ⟨r, he⟩ => by
        cases r <;> exact he⟩⟩
  · refine ⟨?_, ?_, falseToken_necessitating, ?_, ?_, ?_, ?_, ?_⟩
    · intro g f v hc hf
      have hgf : g = f := hc
      subst hgf
      exact hf
    · intro h
      exact ft (h false false true ⟨rfl, rfl⟩).1.1
    · intro w r f g h hc
      have hgf : g = f := hc
      subst hgf
      exact h
    · intro w r hc h
      have hr : r = true := falseToken_contingent_true hc
      have hr' : r = false := h.1
      exact tf (hr.symm.trans hr')
    · exact ⟨⟨rfl, rfl⟩, fun q hq => falseToken_contingent_true hq⟩
    · exact ⟨⟨rfl, rfl⟩, true, True.intro, fun h => tf h.2⟩
    · intro ⟨f, hc, hne⟩
      exact hne ⟨false, rfl, falseToken_contingent_true hc⟩
  · exact ⟨ground_conjunct_sound true, ground_factive true, ground_not_necessitating,
      ground_distribution true, ground_irreflexive true,
      ⟨rfl, fun q hq => ground_contingent hq⟩, ground_contingent_choice true,
      ground_true_noBrute⟩
  · exact ⟨cofinite_sound, cofinite_factive, cofinite_necessitating, cofinite_distribution,
      cofinite_irreflexive, cofinite_no_bccf, cofinite_some_contingent, cofinite_noBrute⟩
  · exact ⟨fun _ _ _ _ h => h, fun _ _ _ h => ⟨h.1, h.1⟩,
      fun _ _ _ _ _ _ h => h, mutual_not_distribution, fun _ _ _ h => h.2 rfl,
      ⟨rfl, fun _ _ => Or.inl rfl⟩, ⟨rfl, true, True.intro, tf⟩, mutual_noBrute⟩
  · exact ⟨fun _ _ _ _ h => h, fun _ _ _ h => ⟨h, h⟩, fun _ _ _ _ _ _ h => h,
      fun _ _ _ _ h _ => h, fun h => h false () ⟨rfl, true, True.intro, tf⟩ rfl,
      ⟨rfl, fun _ _ => True.intro⟩, ⟨rfl, true, True.intro, tf⟩,
      fun ⟨_, hc, hne⟩ => hne ⟨(), hc.1⟩⟩
  · exact ⟨fun _ _ _ _ _ => True.intro, fun _ _ _ _ => ⟨True.intro, True.intro⟩,
      fun _ _ _ _ _ _ _ => True.intro, fun _ _ _ _ h _ => h,
      fun w r hc => (allNecessary_not_contingent w r hc).elim,
      ⟨True.intro, fun _ _ => True.intro⟩, allNecessary_not_contingent,
      fun ⟨_, hc, _⟩ => allNecessary_not_contingent _ _ hc⟩

theorem strengthMap : StrengthMap := by
  refine ⟨fun _ _ _ _ _ h f hc => h f hc.1,
    fun _ _ _ _ _ hc h x hx => h _ ((hc _ x).2 hx),
    fun _ _ _ _ _ h ⟨f, hc, hne⟩ => hne (h f hc),
    ⟨ground_factive false, ground_coherent false, ground_contingentPSR_false false,
      ground_contingent_choice false, ?_⟩,
    ⟨existenceOnly_factive, ?_, ?_, ⟨rfl, true, True.intro, tf⟩,
      fun h => existenceOnly_unexplained false (h .event ⟨rfl, true, True.intro, tf⟩)⟩,
    history_bundle, history_false_hist_unexplained, ⟨.law, rfl, rfl⟩, ?_,
    fun _ _ _ _ _ hr h => h _ (hr _),
    fun _ _ _ _ w hr h f hc => ⟨w, hr w, hc.1, h f hc⟩,
    ⟨?_, ?_, ⟨Or.inr rfl, true, rfl, ?_⟩, ?_⟩,
    ⟨nonReflexiveBare_necessary, ⟨Or.inr rfl, true, rfl, nonReflexiveBare_false⟩,
      fun h => (h true ⟨Or.inr rfl, true, rfl, nonReflexiveBare_false⟩).elim fun _ he => he⟩,
    fun _ _ _ _ _ ⟨r, h⟩ w hw => ⟨r, h w hw⟩,
    ⟨fun _ _ _ _ => ⟨True.intro, True.intro⟩, fun w _ _ => ⟨w, rfl⟩, shifting_not_stable⟩,
    ⟨modalGap_factive, modalGap_distribution, modalGap_contingentPSR_true, ?_,
      modalGap_weak, ?_, modalGap_no_diagonal⟩,
    ⟨diagonal_factive, diagonal_bridge, diagonal_not_distribution, diagonal_weak, ?_⟩,
    fun W B F A a hd hu hw => weak_noBrute A a hd hu hw,
    fun W B F A a he hc => extensional_bridges A a he hc,
    fun W B F A a he hc hf hn hd hi hw c => extensional_weak_collapse A a he hc hf hn hd hi hw c,
    ?_, extensionalGround_bundle,
    ⟨cofinite_factPSR, cofinite_independent, cofinite_closure⟩,
    ⟨?_, ?_, fun _ _ => Iff.rfl, fun _ _ _ h => False.elim h, ⟨rfl, true, True.intro, tf⟩,
      fun h => (h 0 rfl).elim fun _ he => he, fun h => (h 0 ⟨rfl, true, True.intro, tf⟩).elim
        fun _ he => he⟩,
    ⟨?_, ?_, ?_⟩,
    fun W B F A => ⟨rfl, rfl, fun _ f h => ⟨f, rfl, h⟩, ?_, fun _ _ _ h => ⟨h.1 ▸ h.2, h.2⟩⟩,
    fun W B F A w c hc => ⟨fun h => h w c c ⟨rfl, hc.1⟩ hc fun _ _ => Iff.rfl,
      fun h => h w c hc ⟨rfl, hc.1⟩⟩,
    ground_independent, ground_not_necessitating,
    fun W E m => ⟨fun _ _ => Iff.rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
  · intro h
    obtain ⟨r, he⟩ := h .ground True.intro
    cases r with
    | ground => exact ft he
    | choice => exact he
  · intro w x
    cases x
    exact Iff.rfl
  · intro w x _
    exact ⟨.being, True.intro⟩
  · refine ⟨.ground, fun f hc => ?_⟩
    have hf := ground_contingent hc
    subst hf
    exact rfl
  · intro w r f ⟨hw, hr, hf⟩
    exact ⟨Or.inl hr, Or.inr hw⟩
  · intro f hc
    have hf := nonReflexive_contingent hc
    subst hf
    exact ⟨false, rfl, rfl, rfl⟩
  · intro h
    cases h with
    | inl h => exact tf h
    | inr h => exact tf h
  · intro h
    obtain ⟨v, hv, hf, _⟩ := h true ⟨Or.inr rfl, true, rfl, fun h => by
      cases h with
      | inl h => exact tf h
      | inr h => exact tf h⟩
    have hvt : v = true := hv
    subst hvt
    cases hf with
    | inl h => exact tf h
    | inr h => exact tf h
  · intro h
    exact modalGap_unexplained_false
      (h (some false) True.intro true (modalGap_fact_contingent false))
  · intro h
    exact h ⟨true, modalGap_fact_contingent false, modalGap_unexplained_false⟩
  · intro h
    exact h ⟨.fact, diagonal_fact_contingent, diagonal_unexplained_fact⟩
  · refine ⟨fun P => ⟨P (), fun _ => Iff.rfl⟩, fun _ _ => ⟨fun h _ => h, fun h => h ()⟩,
      fun _ _ _ h => h, fun _ _ _ h _ _ _ => h.2, fun _ _ _ _ h hc => ⟨h.1, hc h.2⟩,
      fun _ _ ⟨h, _, _, hn⟩ _ => hn h, fun _ ⟨h, _, _, hn⟩ => (hn h).elim⟩
  · intro w x _
    exact ⟨x + 1, ‹ContingentAt causeOnly.ontic w x›.1, rfl, Nat.succ_ne_self x⟩
  · intro x hx
    exact ⟨x + 1, hx, Nat.succ_ne_self x, rfl⟩
  · intro x _
    cases x with
    | ground => exact ⟨.ground, rfl⟩
    | choice => exact ⟨.ground, rfl⟩
  · intro h
    obtain ⟨y, _, hne, hc⟩ := h .ground True.intro
    cases y with
    | ground => exact hne rfl
    | choice => exact hc
  · intro w x hc
    cases x with
    | ground => exact (hc.2.elim fun _ h => h.2 True.intro).elim
    | choice => exact ⟨.ground, True.intro, hc.1, fun h => GroundFact.noConfusion h⟩
  · intro w r f h v _ hr
    have hrf : r = f := h.1
    subst hrf
    exact hr
  · intro h w x hx
    exact (ofModel_explained m w x).2 (h w x hx)
  · intro h w x hx
    exact (ofModel_explained m w x).1 (h w x hx)
  · intro h w x hc
    exact (ofModel_explained m w x).2 (h w x hc)
  · intro h w x hc
    exact (ofModel_explained m w x).1 (h w x hc)

end TruthCore.Results.Explanation.PSRStrength
