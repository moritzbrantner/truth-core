import TruthCore.Explanation.ActualWorldGap
import TruthCore.Results.Explanation.HistorySelection.Solution
import TruthCore.Results.Explanation.UltimateAdequacy.Solution
namespace TruthCore.Results.Explanation.ActualWorldGap
open TruthCore.Explanation.ActualWorldGap
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive
open TruthCore.Explanation.HistorySelection
open TruthCore.Explanation.PSRStrength hiding history
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower hiding Schema
open TruthCore.Explanation.UltimateAdequacy (Kind groups intrinsic exercise)
set_option autoImplicit false

theorem table_iff_total {W B T : Type} (h : History W B T) (a v : W)
    (ha : LocalRecord h a) (hv : LocalRecord h v) :
    SameTable h v a ↔ SameTotal h v a := by
  constructor
  · intro ht
    refine ⟨fun x t => ?_, ht⟩
    rw [hv.2.2 x t, ha.2.2 x t]
    constructor
    · intro hx
      obtain ⟨y, hy | hy⟩ := hv.2.1 x hx
      · exact (ha.1 _ _ ((ht y x).1 hy)).2
      · exact (ha.1 _ _ ((ht x y).1 hy)).1
    · intro hx
      obtain ⟨y, hy | hy⟩ := ha.2.1 x hx
      · exact (hv.1 _ _ ((ht y x).2 hy)).2
      · exact (hv.1 _ _ ((ht x y).2 hy)).1
  · exact fun h => h.2

theorem table_selects {W B T : Type} (h : History W B T) (a : W) (ha : LocalRecord h a)
    (hall : ∀ v, h.ontic.frame.access a v → LocalRecord h v) :
    ∃ p, EvidenceOnly (tableTruth h) (fun _ => True) p ∧ Selects h p a := by
  apply (TruthCore.Results.Explanation.HistorySelection.characterization h _ _ a).1
  intro v hv he
  exact ((table_iff_total h a v ha (hall v hv)).1
    (fun y x => he (y, x) trivial)).1

theorem refl_total {W B T F : Type} (c : Case W B T F) (a : W) : c.holds a (c.total a) :=
  (c.total_holds a a).2 ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

theorem rival_not_total {W B T F : Type} (c : Case W B T F) {a b : W}
    (hb : Rival c.history a b) : ¬ c.holds b (c.total a) :=
  fun h => hb.2 ((c.total_holds a b).1 h).1

theorem schema : Schema := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R E G S t m
    constructor
    · rintro ⟨ha, hg⟩
      refine ⟨ha, fun g he => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hg g he
      refine ⟨h1, ?_, rfl, h3⟩
      rintro ⟨e1, e2⟩ (he' | he')
      · exact ⟨he'.1, h2 e2 (Or.inl he'.2)⟩
      · exact ⟨he'.1, h2 e2 (Or.inr he'.2)⟩
    · intro g hs s hal hm
      refine ⟨rfl, hs s hal fun e he => ?_⟩
      rcases he with he | he
      · exact (hm (t, e) (Or.inl ⟨rfl, he⟩)).2
      · exact (hm (t, e) (Or.inr ⟨rfl, he⟩)).2
  · intro E G t H I A
    constructor
    · intro e he
      induction he with
      | intrinsic e hi => exact Supply.intrinsic _ ⟨rfl, hi⟩
      | joint g ha _ ih =>
        refine Supply.joint (h := tagged t H) (intrinsic := tagP t I) g ha ?_
        rintro ⟨e1, e2⟩ ⟨rfl, he⟩
        exact ih e2 he
    · intro hp ⟨e1, e2⟩
      constructor
      · rintro ⟨rfl, ha⟩
        rcases (hp e2).1 ha with hi | ⟨g, hg, hef, hc⟩
        · exact Or.inl ⟨rfl, hi⟩
        · refine Or.inr ⟨g, hg, by subst hef; rfl, ?_⟩
          rintro ⟨a1, a2⟩ ⟨rfl, ha'⟩
          exact ⟨rfl, hc a2 ha'⟩
      · rintro (⟨rfl, hi⟩ | ⟨g, hg, hef, hc⟩)
        · exact ⟨rfl, (hp e2).2 (Or.inl hi)⟩
        · have h1 : t = e1 := congrArg Prod.fst hef
          have h2 : H.effect g = e2 := congrArg Prod.snd hef
          subst h1
          exact ⟨rfl, (hp e2).2 (Or.inr ⟨g, hg, h2, fun a ha => (hc (t, a) ⟨rfl, ha⟩).2⟩)⟩
  · intro W B T h a v ha hv
    exact table_iff_total h a v ha hv
  · intro W B T h a ha hall
    exact table_selects h a ha hall
  · intro W B T F c a r ha hall htr hind
    apply hind
    intro v hv
    rw [htr v hv, c.total_holds a v]
    exact table_iff_total c.history a v ha (hall v hv)
  · intro W B T F c a b hb
    exact ⟨fun w => refl_total c w, refl_total c a, b, hb.1, rival_not_total c hb⟩
  · intro W B T F c a b hb hf
    by_cases hex : Explained c.arena a (c.total a)
    · obtain ⟨r, hr⟩ := hex
      by_cases hrb : c.holds b r
      · exact Or.inr (Or.inl ⟨r, hr, hrb, rival_not_total c hb⟩)
      · exact Or.inr (Or.inr ⟨r, hr, hrb, hf r hr, b, hb.1, hrb⟩)
    · exact Or.inl hex
  · intro W B T F c a b r hb hn ha he
    exact necessary_discriminating_excludes_rival c.history c.holds a b r hn
      ⟨ha, fun v hv hr => ((c.total_holds a v).1 (he v hv hr)).1⟩ hb.1 hb.2
  · intro W B T F c a b hb hc hwf
    have key : ∀ f, c.holds a f → ¬ c.holds b f → False := by
      intro f
      induction f using hwf.induction with
      | _ f ih =>
        intro ha hnb
        obtain ⟨r, hr, hra, hrb⟩ := hc b hb f ha hnb
        exact ih r hr hra hrb
    exact key _ (refl_total c a) (rival_not_total c hb)

/-! ## Causal forms -/
theorem edge_recorded (k : Kind) (n : Nat) :
    ∃ m, (groups k).graph.edge m n ∨ (groups k).graph.edge n m := by
  cases k with
  | single =>
    cases n with
    | zero => exact ⟨1, Or.inr ⟨0, trivial, rfl, Or.inl rfl⟩⟩
    | succ n => exact ⟨0, Or.inl ⟨n, trivial, rfl, Or.inl rfl⟩⟩
  | plural =>
    match n with
    | 0 => exact ⟨2, Or.inr ⟨0, trivial, rfl, Or.inl (Or.inl rfl)⟩⟩
    | 1 => exact ⟨2, Or.inr ⟨0, trivial, rfl, Or.inl (Or.inr rfl)⟩⟩
    | n+2 => exact ⟨0, Or.inl ⟨n, trivial, rfl, Or.inl (Or.inl rfl)⟩⟩
  | branch =>
    cases n with
    | zero => exact ⟨1, Or.inr ⟨0, trivial, rfl, Or.inl (Or.inl rfl)⟩⟩
    | succ n => exact ⟨0, Or.inl ⟨n, trivial, rfl, Or.inl (Or.inl rfl)⟩⟩
  | chain => exact ⟨n + 1, Or.inl ⟨n, trivial, rfl, Or.inl (Or.inl rfl)⟩⟩

theorem local_record (o k p) (w : World) : LocalRecord (history o k p) w := by
  refine ⟨?_, ?_, fun _ _ => Iff.rfl⟩
  · intro y x h
    match y, x, h with
    | none, some _, h => exact ⟨h.1, h.2⟩
    | some _, some _, h => exact ⟨h.1, h.2.1⟩
  · intro x hx
    cases x with
    | none =>
      have hp : p = .ground := hx
      exact ⟨some (w.1, 0), Or.inr ⟨hp, rfl⟩⟩
    | some x =>
      obtain ⟨m, hm⟩ := edge_recorded k x.2
      have hx' : x.1 = w.1 := hx
      refine ⟨some (x.1, m), ?_⟩
      rcases hm with hm | hm
      · exact Or.inl ⟨hx', hx', hm⟩
      · exact Or.inr ⟨hx', hx', hm⟩

theorem rival_rival (k p) : Rival (history true k p) actual rival := by
  refine ⟨Or.inl rfl, fun h => ?_⟩
  have h1 : (true, 0).1 = (false, true).1 := (h (some (true, 0)) 0).1 rfl
  exact Bool.noConfusion h1

theorem rival_tag {o k p} {b : World} (h : Rival (history o k p) actual b) : b.1 = true := by
  cases hb : b.1 with
  | true => rfl
  | false => exact (h.2 (same_of_tag o k p (hb.trans rfl)).1).elim

theorem edge_iff (k) (t : Bool) (y x : Bool × Nat) :
    (y.1 = t ∧ x.1 = t ∧ (groups k).graph.edge y.2 x.2) ↔ (tagged t (groups k)).graph.edge y x := by
  constructor
  · rintro ⟨h1, h2, g, ha, he, hm⟩
    refine ⟨g, ha, ?_, ?_⟩
    · exact Prod.ext h2.symm he
    · rcases hm with hm | hm
      · exact Or.inl ⟨h1, hm⟩
      · exact Or.inr ⟨h1, hm⟩
  · rintro ⟨g, ha, he, hm⟩
    have h2 : t = x.1 := congrArg Prod.fst he
    have h3 : (groups k).effect g = x.2 := congrArg Prod.snd he
    rcases hm with hm | hm
    · exact ⟨hm.1, h2.symm, g, ha, h3, Or.inl hm.2⟩
    · exact ⟨hm.1, h2.symm, g, ha, h3, Or.inr hm.2⟩

/-- Sources in the three source forms: index zero has no incoming edge. -/
theorem no_edge_zero (k : Kind) (hk : k ≠ .chain) (m : Nat) : ¬ (groups k).graph.edge m 0 := by
  rintro ⟨g, _, he, _⟩
  cases k with
  | single => exact Nat.succ_ne_zero g he
  | plural => exact Nat.succ_ne_zero (g + 1) he
  | branch => exact Nat.succ_ne_zero g he
  | chain => exact hk rfl

theorem edge_lt_single {m n : Nat} (h : (groups .single).graph.edge m n) : m < n := by
  obtain ⟨g, _, he, hm⟩ := h
  rcases hm with hm | hm
  · have hm0 : m = 0 := hm
    have hn : n = g + 1 := he.symm
    omega
  · exact hm.elim

theorem edge_lt_plural {m n : Nat} (h : (groups .plural).graph.edge m n) : m < n := by
  obtain ⟨g, _, he, hm⟩ := h
  rcases hm with hm | hm
  · have hm0 : m = 0 ∨ m = 1 := hm
    have hn : n = g + 2 := he.symm
    omega
  · exact hm.elim

def rank : Fact → Nat
  | .member x => x.2
  | .total _ => 1
  | .record _ => 1
  | .ground => 0
  | .marker => 0

theorem internal_wf (o k) (hlt : ∀ m n, (groups k).graph.edge m n → m < n) :
    WellFounded ((case o k .internal).explains actual) := by
  refine Subrelation.wf (r := InvImage (· < ·) rank) ?_ (InvImage.wf rank Nat.lt_wfRel.wf)
  intro r f h
  change rank r < rank f
  cases r <;> cases f <;> simp only [case, reasonFor] at h
  case member.member y x => exact hlt _ _ h.2.2
  case member.total y t => rw [h.2.2]; simp [rank]
  case member.record y t => rw [h.2.2]; simp [rank]
  all_goals
    first
      | exact absurd h.1 (by decide)

theorem internal_closure_chain (o) : ContrastiveClosure (case o .chain .internal) actual := by
  intro b hb f ha hnb
  have hbt : b.1 = true := rival_tag hb
  have sep : ∀ n, holdsAt .internal actual (.member (false, n)) ∧
      ¬ holdsAt .internal b (.member (false, n)) := fun n =>
    ⟨rfl, fun h => Bool.noConfusion (h.trans hbt)⟩
  cases f with
  | member x =>
    obtain ⟨t, n⟩ := x
    have ht : t = false := ha
    subst ht
    exact ⟨.member (false, n + 1), ⟨rfl, rfl, n, trivial, rfl, Or.inl (Or.inl rfl)⟩,
      (sep _).1, (sep _).2⟩
  | total t =>
    have ht : t = false := ha
    subst ht
    exact ⟨.member (false, 0), ⟨rfl, rfl, rfl⟩, (sep _).1, (sep _).2⟩
  | record t =>
    have ht : t = false := ha
    subst ht
    exact ⟨.member (false, 0), ⟨rfl, rfl, rfl⟩, (sep _).1, (sep _).2⟩
  | ground => exact absurd ha (by simp [case, holdsAt])
  | marker => exact absurd ha.1 (by decide)

theorem internal_closure_iff (k) : ContrastiveClosure (case true k .internal) actual ↔ k = .chain := by
  constructor
  · intro hc
    by_contra hk
    obtain ⟨r, hr, _, _⟩ := hc rival (rival_rival k .internal) (.member (false, 0)) rfl
      (fun h => Bool.noConfusion h)
    cases r with
    | member y => exact no_edge_zero k hk _ hr.2.2
    | ground => exact absurd hr.1 (by decide)
    | total _ => exact hr
    | record _ => exact hr
    | marker => exact hr
  · rintro rfl
    exact internal_closure_chain true

theorem chain_not_wf : ¬ WellFounded ((case true .chain .internal).explains actual) := fun hwf =>
  schema.2.2.2.2.2.2.2.2 _ _ _ _ (case true .chain .internal) actual rival
    (rival_rival .chain .internal) (internal_closure_chain true) hwf

theorem not_closure_of_total {k p} (hrb : ∀ r, reasonFor k p actual r (.total false) →
    holdsAt p rival r) : ¬ ContrastiveClosure (case true k p) actual := by
  intro hc
  obtain ⟨r, hr, _, hn⟩ := hc rival (rival_rival k p) (.total false) rfl (fun h => Bool.noConfusion h)
  exact hn (hrb r hr)

theorem exercise_background (k) (t : Bool) :
    (taggedExercise t (exercise k)).coherent ∧
    (∀ g, (taggedExercise t (exercise k)).jointlySufficient g) ∧
    LocalPower (tagged t (groups k)) (tagP t (intrinsic k))
      (tagP t ((exercise k).occurs (exercise k).actual)) := by
  obtain ⟨hco, hs, _, hl, _⟩ := TruthCore.Results.Explanation.UltimateAdequacy.certificate.1.1 k
  exact ⟨(schema.1 _ _ _ _ t _).1 hco, fun g => (schema.1 _ _ _ _ t _).2 g (hs g),
    (schema.2.1 _ _ t _ _ _).2 hl⟩

theorem same_evidence_anonymous (k p) (v w : World) :
    SameEvidence (anonymous k p) (fun _ => True) v w := by
  intro e _
  have key : ∀ u : World, anonymous k p u e ↔ (groups k).graph.edge e.1 e.2 := by
    intro u
    constructor
    · rintro ⟨y, x, ⟨_, _, he⟩, h1, h2⟩
      rw [← h1, ← h2]
      exact he
    · intro he
      exact ⟨(u.1, e.1), (u.1, e.2), ⟨rfl, rfl, he⟩, rfl, rfl⟩
  rw [key v, key w]

theorem no_anonymous (k p) (a : World) : ¬ ∃ q, EvidenceOnly (anonymous k p) (fun _ => True) q ∧
    Selects (history true k p) q a := by
  let b : World := (!a.1, a.2)
  have hne : ¬ SameHistory (history true k p) b a := by
    intro h
    have h1 := (h (some (a.1, 0)) 0).2 rfl
    have h2 : a.1 = !a.1 := h1
    cases ha : a.1 <;> simp [ha] at h2
  exact TruthCore.Results.Explanation.HistorySelection.no_selection _ _ _ a b (Or.inl rfl) hne
    (same_evidence_anonymous k p b a)

theorem ground_psr (k) (w : World) : ContingentPSR (case true k .ground).arena w := by
  rintro f ⟨hf, v, _, hnv⟩
  cases f with
  | member x => exact ⟨.ground, rfl, hf⟩
  | total t => exact ⟨.ground, rfl, hf⟩
  | record t => exact ⟨.ground, rfl, hf⟩
  | ground => exact (hnv rfl).elim
  | marker => exact absurd hf.1 (by decide)

theorem brute_unexplained (k) : ¬ Explained (case true k .brute).arena actual (.total false) := by
  rintro ⟨r, h⟩
  cases r with
  | member _ => exact absurd h.1 (by decide)
  | record _ => exact absurd h.1 (by decide)
  | ground => exact absurd h.1 (by decide)
  | marker => exact absurd h.1 (by decide)
  | total _ => exact h

theorem total_contingent (k p) : Contingent (case true k p).arena actual (.total false) :=
  ⟨rfl, rival, Or.inl rfl, fun h => Bool.noConfusion h⟩

theorem copy_closure_chain : ContrastiveClosure (case true .chain .copy) actual := by
  intro b hb f ha hnb
  have hbt : b.1 = true := rival_tag hb
  have ne : ¬ (false = b.1) := fun h => Bool.noConfusion (h.trans hbt)
  cases f with
  | member x =>
    obtain ⟨t, n⟩ := x
    have ht : t = false := ha
    subst ht
    exact ⟨.member (false, n + 1), ⟨rfl, rfl, n, trivial, rfl, Or.inl (Or.inl rfl)⟩, rfl, ne⟩
  | total t =>
    have ht : t = false := ha
    subst ht
    exact ⟨.record false, ⟨rfl, rfl, rfl⟩, rfl, ne⟩
  | record t =>
    have ht : t = false := ha
    subst ht
    exact ⟨.total false, ⟨rfl, rfl, rfl⟩, rfl, ne⟩
  | ground => exact absurd (show Policy.copy = .ground from ha) (by decide)
  | marker => exact absurd ha.1 (by decide)

theorem ground_factive (k) : Factive (case true k .ground).arena := by
  intro w r f h
  cases r with
  | ground =>
    cases f with
    | member _ => exact ⟨rfl, h.2⟩
    | total _ => exact ⟨rfl, h.2⟩
    | record _ => exact ⟨rfl, h.2⟩
    | ground => exact h.elim
    | marker => exact h.elim
  | member y =>
    cases f with
    | member _ => exact ⟨h.1, h.2.1⟩
    | total _ => exact absurd h.1 (by decide)
    | record _ => exact absurd h.1 (by decide)
    | ground => exact h.elim
    | marker => exact h.elim
  | total _ =>
    cases f with
    | record _ => exact absurd h.1 (by decide)
    | _ => exact h.elim
  | record _ =>
    cases f with
    | total _ => exact absurd h.1 (by decide)
    | _ => exact h.elim
  | marker =>
    cases f with
    | total _ => exact absurd h.1 (by decide)
    | _ => exact h.elim

theorem law_no_reason (k) (r : Fact) : ¬ reasonFor k .law actual r .marker := by
  intro h
  cases r <;> exact h

theorem internal_chain_psr (w : World) : ContingentPSR (case true .chain .internal).arena w := by
  rintro f ⟨hf, -⟩
  cases f with
  | member x => exact ⟨.member (x.1, x.2 + 1), hf, hf, x.2, trivial, rfl, Or.inl (Or.inl rfl)⟩
  | total t => exact ⟨.member (t, 0), rfl, hf, rfl⟩
  | record t => exact ⟨.member (t, 0), rfl, hf, rfl⟩
  | ground => exact absurd (show Policy.internal = .ground from hf) (by decide)
  | marker => exact absurd hf.1 (by decide)

theorem copy_chain_psr (w : World) : ContingentPSR (case true .chain .copy).arena w := by
  rintro f ⟨hf, -⟩
  cases f with
  | member x => exact ⟨.member (x.1, x.2 + 1), hf, hf, x.2, trivial, rfl, Or.inl (Or.inl rfl)⟩
  | total t => exact ⟨.record t, rfl, rfl, hf⟩
  | record t => exact ⟨.total t, rfl, rfl, hf⟩
  | ground => exact absurd (show Policy.copy = .ground from hf) (by decide)
  | marker => exact absurd hf.1 (by decide)

theorem controls : TruthCore.Explanation.ActualWorldGap.Controls := by
  have cert := TruthCore.Results.Explanation.UltimateAdequacy.certificate.1
  refine ⟨local_record, rival_rival, exercise_background, fun o k p w y x => edge_iff k w.1 y x,
    fun t e => (schema.2.1 _ _ t _ _ (fun _ => True)).1 e (cert.2.1 e),
    fun t e => (schema.2.1 _ _ t _ _ (fun _ => True)).1 e (cert.2.2.2.1 e),
    fun k p a => table_selects _ a (local_record _ _ _ _) (fun _ _ => local_record _ _ _ _),
    no_anonymous, ?_, ?_, ?_, ?_, internal_closure_iff,
    internal_wf true .single (fun _ _ => edge_lt_single),
    internal_wf true .plural (fun _ _ => edge_lt_plural), chain_not_wf, internal_chain_psr, ?_,
    fun _ => ⟨.record false, rfl, rfl, rfl⟩, copy_closure_chain, copy_chain_psr, ?_, ?_, ?_, ?_, ?_,
    ?_, internal_wf false .single (fun _ _ => edge_lt_single), ?_, ?_, ?_⟩
  · exact fun k => ⟨brute_unexplained k, fun h => brute_unexplained k (h _ (total_contingent k _)),
      fun hc => by
        obtain ⟨r, hr, _, _⟩ := hc rival (rival_rival k .brute) (.total false) rfl
          (fun h => Bool.noConfusion h)
        exact brute_unexplained k ⟨r, hr⟩⟩
  · intro w x hx
    cases x with
    | none => exact absurd (show Policy.brute = .ground from hx) (by decide)
    | some x => exact ⟨.member (x.1, x.2 + 1), hx, hx, x.2, trivial, rfl, Or.inl (Or.inl rfl)⟩
  · intro hl
    refine brute_unexplained .chain (hl ?_)
    intro g hg
    cases g with
    | member x =>
      exact ⟨.member (x.1, x.2 + 1), hg, hg, x.2, trivial, rfl, Or.inl (Or.inl rfl)⟩
    | _ => exact hg.elim
  · intro k
    exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rival, Or.inl rfl, fun h => Bool.noConfusion h⟩,
      fun h => Bool.noConfusion h, fun h => h fun _ _ => Iff.rfl⟩
  · intro k
    refine ⟨⟨rfl, rfl, rfl⟩, fun v => ?_, fun h => h fun _ _ => Iff.rfl⟩
    constructor
    · intro hv
      exact (same_of_tag true k .copy hv.symm).2
    · intro ht
      exact (total_iff true k .copy actual v).2
        ((table_iff_total _ actual v (local_record _ _ _ _) (local_record _ _ _ _)).1 ht)
  · intro k
    refine ⟨ground_psr k, ground_factive k, ?_, ⟨rfl, rfl⟩, fun _ => rfl,
      fun h => Bool.noConfusion h, ?_, ?_⟩
    · intro h
      exact Bool.noConfusion (h actual .ground (.total false) ⟨rfl, rfl⟩ rival (Or.inl rfl) rfl)
    · intro h
      exact Bool.noConfusion ((h rival (Or.inl rfl)).1 rfl)
    · apply not_closure_of_total
      intro r hr
      cases r with
      | ground => rfl
      | member _ => exact absurd hr.1 (by decide)
      | record _ => exact absurd hr.1 (by decide)
      | marker => exact absurd hr.1 (by decide)
      | total _ => exact hr.elim
  · intro k
    refine ⟨⟨rfl, rfl, rfl⟩, ⟨⟨rfl, rfl⟩, rival, Or.inl rfl, fun h => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · exact absurd h.2 (by decide)
    · rintro v ⟨_, rfl⟩
      rfl
    · intro h
      exact absurd ((h duplicate (Or.inl rfl)).2 rfl).2 (by decide)
    · rintro ⟨r, hr⟩
      exact law_no_reason k r hr
    · intro hp
      obtain ⟨r, hr⟩ := hp .marker ⟨⟨rfl, rfl⟩, rival, Or.inl rfl, fun h => absurd h.2 (by decide)⟩
      exact law_no_reason k r hr
    · intro hc
      obtain ⟨r, hr, _, _⟩ := hc rival (rival_rival k .law) .marker ⟨rfl, rfl⟩
        (fun h => absurd h.2 (by decide))
      exact law_no_reason k r hr
  · rintro k p b ⟨h | h, hne⟩
    · exact Bool.noConfusion h
    · subst h
      exact hne fun _ _ => Iff.rfl
  · rintro k p ⟨_, v, h | h, hnv⟩
    · exact Bool.noConfusion h
    · subst h
      exact hnv rfl
  · intro k
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    rintro v (h | h)
    · exact Bool.noConfusion h
    · subst h
      exact ⟨rfl, rfl⟩
  · rintro b ⟨h | h, hne⟩
    · exact Bool.noConfusion h
    · subst h
      exact (hne fun _ _ => Iff.rfl).elim
  · refine ⟨fun _ _ => Iff.rfl, fun h => ?_, fun h => ?_, fun _ _ hc => hc.elim, fun _ _ => Iff.rfl⟩
    · exact Bool.noConfusion ((h.1 false 0).2 rfl)
    · obtain ⟨_, hy | hy⟩ := h true rfl <;> exact hy
  · refine ⟨fun _ _ => Iff.rfl, fun h => ?_, fun h => ?_, fun _ hx => ?_, fun _ _ => Iff.rfl⟩
    · exact Bool.noConfusion ((h.1 () 0).2 rfl)
    · exact Bool.noConfusion (h () () trivial).1
    · exact Bool.noConfusion hx
  · refine ⟨fun _ _ => Iff.rfl, fun h => ?_, fun h => ?_, fun _ _ _ => ⟨trivial, trivial⟩,
      fun _ _ => ⟨(), Or.inl trivial⟩⟩
    · rcases (h.1 () 1).2 (Or.inr rfl) with h1 | h1
      · exact Nat.succ_ne_zero 0 h1
      · exact Bool.noConfusion h1
    · rcases (h () 1).2 trivial with h1 | h1
      · exact Nat.succ_ne_zero 0 h1
      · exact Bool.noConfusion h1

end TruthCore.Results.Explanation.ActualWorldGap
