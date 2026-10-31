import TruthCore.Explanation.PathRelocation
import TruthCore.Results.Explanation.HistorySelection.Solution

namespace TruthCore.Results.Explanation.PathRelocation
open TruthCore.Explanation.PathRelocation
open TruthCore.Explanation.HistorySelection
open TruthCore.Modal.TemporalHistory TruthCore.Modal.HistoryContrastive
open TruthCore.Results.Explanation.HistorySelection (no_selection characterization)

theorem symmetry_transfer {T S : Type} (σ : T → T) (C : (T → S) → Prop) (f : T → S)
    (hσ : InvariantUnder σ C) (hu : UniqueSolution C f) : f ∘ σ = f :=
  hu.2 _ (hσ f hu.1)

theorem constant_of_stationary {S : Type} (f : Int → S)
    (h : ∀ t, f (t + 1) = f t) : ∀ t, f t = f 0 := by
  intro t
  induction t using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [h]; exact ih
  | pred i ih =>
    have := h (-(i : Int) - 1)
    rw [show -(i : Int) - 1 + 1 = -(i : Int) by omega] at this
    rw [← this]; exact ih

theorem stationary {S : Type} (C : (Int → S) → Prop) (f : Int → S)
    (hC : ShiftInvariant C) (hu : UniqueSolution C f) :
    ¬ Changes f ∧ ∀ t, f t = f 0 := by
  have hs : ∀ t, f (t + 1) = f t := fun t =>
    congrFun (symmetry_transfer _ C f hC hu) t
  exact ⟨fun ⟨t, ht⟩ => ht (hs t), constant_of_stationary f hs⟩

theorem follows_invariant {S : Type} (R : Int → S → S → Prop) (hR : Autonomous R) :
    ShiftInvariant (Follows R) := by
  intro f hf t
  have := hf (t + 1)
  rw [hR t] at this
  exact this

theorem global_invariant : ShiftInvariant GlobalLaw := fun _ hf t => hf (t + 1)

theorem global_unique : UniqueSolution GlobalLaw fixedSignal := by
  have hu := TruthCore.Results.Causality.UniqueFeedback.controls
  exact ⟨fun _ => hu.2.1, fun signal hs => funext (fun t => hu.2.2 (signal t) (hs t))⟩

theorem same_history_iff {S : Type} (C : (Int → S) → Prop) (v w : {g // C g}) :
    SameHistory (pathHistory C) v w ↔ v.1 = w.1 := by
  constructor
  · intro h
    funext t
    have hw : w.1 t = v.1 t := (h (w.1 t) t).mpr rfl
    exact hw.symm
  · intro h x t
    change x = v.1 t ↔ x = w.1 t
    rw [h]

theorem shift_differs {S : Type} (C : (Int → S) → Prop) (hC : ShiftInvariant C)
    (a : {g // C g}) (hch : Changes a.1) :
    ¬ SameHistory (pathHistory C) (shiftWorld hC a) a := by
  intro h
  obtain ⟨t, ht⟩ := hch
  exact ht (congrFun ((same_history_iff C _ _).mp h) t)

theorem not_determines {S R : Type} (C : (Int → S) → Prop) (hC : ShiftInvariant C)
    (a : {g // C g}) (truth : {g // C g} → R → Prop) (basis : R → Prop)
    (hch : Changes a.1) (he : SameEvidence truth basis (shiftWorld hC a) a) :
    ¬ Determines (pathHistory C) truth basis a :=
  fun hd => shift_differs C hC a hch (hd _ trivial he)

theorem law_only {S R : Type} (C : (Int → S) → Prop) (a : {g // C g}) (P : R → Prop)
    (basis : R → Prop) :
    Determines (pathHistory C) (fun _ r => P r) basis a ↔ ∀ g, C g → g = a.1 := by
  constructor
  · intro hd g hg
    exact (same_history_iff C ⟨g, hg⟩ a).mp (hd ⟨g, hg⟩ trivial (fun _ _ => Iff.rfl))
  · intro h v _ _
    exact (same_history_iff C v a).mpr (h v.1 v.2)

theorem token_iff {S : Type} (C : (Int → S) → Prop) (a v : {g // C g}) :
    SameEvidence transitionTruth (fun _ => True) v a ↔
      SameHistory (pathHistory C) v a := by
  rw [same_history_iff]
  constructor
  · intro he
    funext t
    have := (he (t, a.1 t, a.1 (t + 1)) trivial).mpr ⟨rfl, rfl⟩
    exact this.1
  · intro h r _
    change (v.1 r.1 = r.2.1 ∧ v.1 (r.1 + 1) = r.2.2) ↔
      (a.1 r.1 = r.2.1 ∧ a.1 (r.1 + 1) = r.2.2)
    rw [h]

theorem token_determines {S : Type} (C : (Int → S) → Prop) (a : {g // C g}) :
    Determines (pathHistory C) transitionTruth (fun _ => True) a :=
  fun v _ he => (token_iff C a v).mp he

theorem token_coextensive {S : Type} (C : (Int → S) → Prop) (a v : {g // C g})
    (p : {g // C g} → Prop)
    (hp : EvidenceOnly transitionTruth (fun _ => True) p)
    (hs : Selects (pathHistory C) p a) :
    p v ↔ SameHistory (pathHistory C) v a :=
  ⟨fun hv => hs.2 v trivial hv,
    fun h => (hp v a ((token_iff C a v).mpr h)).mpr hs.1⟩

theorem copy_unique {S : Type} (f : Int → S) :
    UniqueSolution (Follows (copyLaw f)) f :=
  ⟨fun _ => ⟨rfl, rfl⟩, fun _ hg => funext (fun t => (hg t).1)⟩

theorem copy_injective {S : Type} (f g : Int → S) : copyLaw f = copyLaw g ↔ f = g := by
  constructor
  · intro h
    apply (copy_unique g).2
    rw [← h]
    exact (copy_unique f).1
  · rintro rfl
    rfl

theorem graph_follows {S : Type} (f : Int → S) : Follows (fun _ => graphLaw f) f :=
  fun t => ⟨t, rfl, rfl⟩

theorem graph_dating {S : Type} (f g : Int → S) (hf : Function.Injective f)
    (hg : Follows (fun _ => graphLaw f) g) : SameUpToDating f g := by
  obtain ⟨k, hk, -⟩ := hg 0
  refine ⟨k, fun t => ?_⟩
  induction t using Int.induction_on with
  | zero => simpa using hk
  | succ i ih =>
    obtain ⟨u, hu, hu'⟩ := hg (i : Int)
    have : u = (i : Int) + k := hf (hu.symm.trans ih)
    rw [hu', this]
    congr 1
    omega
  | pred i ih =>
    obtain ⟨u, hu, hu'⟩ := hg (-(i : Int) - 1)
    rw [show -(i : Int) - 1 + 1 = -(i : Int) by omega] at hu'
    have : u + 1 = -(i : Int) + k := hf (hu'.symm.trans ih)
    rw [hu]
    congr 1
    omega

theorem graph_eq_of_dating {S : Type} (f g : Int → S) (h : SameUpToDating f g) :
    graphLaw f = graphLaw g := by
  obtain ⟨k, hk⟩ := h
  funext s s'
  apply propext
  constructor
  · rintro ⟨t, rfl, rfl⟩
    refine ⟨t - k, ?_, ?_⟩
    · rw [hk]; congr 1; omega
    · rw [hk]; congr 1; omega
  · rintro ⟨t, rfl, rfl⟩
    refine ⟨t + k, hk t, ?_⟩
    rw [hk]; congr 1; omega

theorem functional_excludes {S : Type} (r : S → S → Prop) (f : Int → S) (t u : Int)
    (hr : ∀ s a b, r s a → r s b → a = b) (hf : Follows (fun _ => r) f)
    (h : f t = f u) : f (t + 1) = f (u + 1) := by
  have ht := hf t
  have hu := hf u
  simp only at ht hu
  rw [h] at ht
  exact hr _ _ _ ht hu

theorem finite_bijective {S : Type} (n : Nat) (step : S → S) :
    Function.Bijective (fun f : {f : Fin (n + 1) → S //
      FollowsFin (fun a b => b = step a) f} => f.1 0) := by
  constructor
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    apply Subtype.ext
    funext i
    induction i using Fin.induction with
    | zero => exact h
    | succ i ih =>
      have hfi : f i.succ = step (f i.castSucc) := hf i
      have hgi : g i.succ = step (g i.castSucc) := hg i
      have ih' : f i.castSucc = g i.castSucc := ih
      change f i.succ = g i.succ
      rw [hfi, hgi, ih']
  · intro s
    refine ⟨⟨fun i => step^[(i : Nat)] s, fun i => ?_⟩, rfl⟩
    simp [Function.iterate_succ_apply']

theorem splice_follows {S : Type} (R : Int → S → S → Prop) (f g : Int → S) (t₀ : Int)
    (hf : Follows R f) (hg : Follows R g) (h : f t₀ = g t₀) :
    Follows R (splice f g t₀) := by
  intro t
  unfold splice
  by_cases h1 : t + 1 ≤ t₀
  · rw [ite_eq_left (by omega : t ≤ t₀), ite_eq_left h1]
    exact hf t
  · rw [ite_eq_right h1]
    by_cases h2 : t ≤ t₀
    · have : t = t₀ := by omega
      subst this
      rw [ite_eq_left h2, h]
      exact hg t
    · rw [ite_eq_right h2]
      exact hg t

theorem edge_increases {S : Type} (f : Int → S) {x y : Int × S}
    (h : Relation.TransGen (TemporalEdge f) x y) : x.1 < y.1 := by
  induction h with
  | single hxy => have := hxy.2.2; omega
  | tail _ hyz ih => have := hyz.2.2; omega

theorem no_cycle {S : Type} (f : Int → S) (x : Int × S) :
    ¬ Relation.TransGen (TemporalEdge f) x x :=
  fun h => lt_irrefl _ (edge_increases f h)

theorem predecessor_edge {S : Type} (f : Int → S) (t : Int) :
    TemporalEdge f (t - 1, f (t - 1)) (t, f t) :=
  ⟨rfl, rfl, by simp⟩

theorem certificate : TruthCore.Explanation.PathRelocation.Certificate := by
  refine ⟨fun _ _ σ C f hσ hu => symmetry_transfer σ C f hσ hu,
    fun _ C f hC hu => stationary C f hC hu,
    fun _ R f hR hu => (stationary _ f (follows_invariant R hR) hu).1,
    ?_, ⟨global_invariant, global_unique, (stationary _ _ global_invariant global_unique).1⟩,
    ?_, ?_, fun _ _ C a P basis => law_only C a P basis,
    fun _ C a v => ⟨token_iff C a v, token_determines C a,
      fun p hp hs => token_coextensive C a v p hp hs⟩,
    fun _ f g => ⟨copy_unique f, copy_injective f g⟩, ?_,
    fun _ r f t u hr hf h => functional_excludes r f t u hr hf h,
    fun _ n step => finite_bijective n step,
    fun _ R f g t₀ hf hg h => splice_follows R f g t₀ hf hg h,
    fun _ f => ⟨no_cycle f, predecessor_edge f⟩⟩
  · intro S R f k hk hu t
    have hinv : InvariantUnder (fun t : Int => t + k) (Follows R) := by
      intro g hg u
      have := hg (u + k)
      rw [hk u, show u + k + 1 = u + 1 + k by omega] at this
      exact this
    exact congrFun (symmetry_transfer _ _ f hinv hu) t
  · intro S R C hC a truth basis hch he
    exact ⟨not_determines C hC a truth basis hch he,
      no_selection (pathHistory C) truth basis a (shiftWorld hC a) trivial
        (shift_differs C hC a hch) he⟩
  · intro S R C hC a truth basis hch hd
    by_contra hne
    apply not_determines C hC a truth basis hch _ hd
    intro r hr
    by_contra hn
    exact hne ⟨r, hr, hn⟩
  · intro S f g hf
    refine ⟨graph_follows f, graph_dating f g hf, fun hg => ⟨?_, graph_eq_of_dating f g⟩⟩
    intro h
    apply graph_dating f g hf
    rw [h]
    exact graph_follows g

/-! Controls. -/

theorem alt_succ (t : Int) : alt (t + 1) = !alt t := by
  unfold alt
  rcases Int.emod_two_eq t with h | h
  · have h' : (t + 1) % 2 = 1 := by omega
    simp [h, h']
  · have h' : (t + 1) % 2 = 0 := by omega
    simp [h, h']

theorem alt_follows : Follows (fun _ => flip) alt := alt_succ

theorem alt_changes : Changes alt := ⟨0, by decide⟩

theorem flip_unique_from (g h : Int → Bool) (hg : Follows (fun _ => flip) g)
    (hh : Follows (fun _ => flip) h) (h0 : g 0 = h 0) : g = h := by
  funext t
  induction t using Int.induction_on with
  | zero => exact h0
  | succ i ih =>
    have h1 : g ((i : Int) + 1) = !g i := hg i
    have h2 : h ((i : Int) + 1) = !h i := hh i
    rw [h1, h2, ih]
  | pred i ih =>
    have h1 : g (-(i : Int) - 1 + 1) = !g (-(i : Int) - 1) := hg _
    have h2 : h (-(i : Int) - 1 + 1) = !h (-(i : Int) - 1) := hh _
    rw [show -(i : Int) - 1 + 1 = -(i : Int) by omega] at h1 h2
    rw [ih, h2] at h1
    simpa using h1.symm

theorem flip_autonomous : Autonomous (fun _ : Int => flip) := fun _ => rfl

theorem flip_invariant : ShiftInvariant (Follows (fun _ => flip) (S := Bool)) :=
  follows_invariant _ flip_autonomous

theorem flip_cases (g : Int → Bool) (hg : Follows (fun _ => flip) g) :
    g = alt ∨ g = alt ∘ (fun t : Int => t + 1) := by
  cases h : g 0 with
  | true => exact Or.inl (flip_unique_from g alt hg alt_follows (by rw [h]; decide))
  | false =>
    exact Or.inr (flip_unique_from g _ hg (flip_invariant alt alt_follows) (by rw [h]; decide))

theorem alt_shift_ne : alt ∘ (fun t : Int => t + 1) ≠ alt :=
  fun h => absurd (congrFun h 0) (by decide)

theorem flip_dating (g : Int → Bool) (hg : Follows (fun _ => flip) g) :
    SameUpToDating alt g := by
  rcases flip_cases g hg with rfl | rfl
  · exact ⟨0, fun t => by simp⟩
  · exact ⟨1, fun _ => rfl⟩

theorem flip_law_fails (a : {g // Follows (fun _ => flip) g}) :
    ¬ Determines (pathHistory (Follows (fun _ => flip)))
        (fun _ (_ : Unit) => True) (fun _ => True) a := by
  intro hd
  have hch : Changes a.1 := by
    rcases flip_cases a.1 a.2 with h | h
    · rw [h]; exact alt_changes
    · rw [h]; exact ⟨0, by decide⟩
  exact not_determines _ flip_invariant a _ _ hch (fun _ _ => Iff.rfl) hd

theorem pinned_unique : UniqueSolution pinned alt :=
  ⟨⟨alt_follows, by decide⟩, fun g hg =>
    flip_unique_from g alt hg.1 alt_follows (by rw [hg.2]; decide)⟩

theorem pinned_not_invariant : ¬ ShiftInvariant pinned := by
  intro h
  have := (h alt pinned_unique.1).2
  exact absurd this (by decide)

theorem stay_follows : Follows (fun _ => rise) stayFalse := fun _ h => by cases h

theorem rise_follows : Follows (fun _ => rise) riseAtOne := by
  intro t h
  simp only [riseAtOne, decide_eq_true_eq] at h ⊢
  omega

theorem branch_fails (h : Follows (fun _ => rise) stayFalse) :
    ¬ Determines (pathHistory (Follows (fun _ => rise)))
        transitionTruth upToNow ⟨stayFalse, h⟩ := by
  intro hd
  have hs := hd ⟨riseAtOne, rise_follows⟩ trivial (by
    rintro ⟨t, s, s'⟩ hr
    have ht : t < 0 := hr
    have e1 : riseAtOne t = false := by simp [riseAtOne]; omega
    have e2 : riseAtOne (t + 1) = false := by simp [riseAtOne]; omega
    change (riseAtOne t = s ∧ riseAtOne (t + 1) = s') ↔ (false = s ∧ false = s')
    rw [e1, e2])
  have h1 : riseAtOne 1 = stayFalse 1 := congrFun ((same_history_iff _ _ _).mp hs) 1
  exact absurd h1 (by decide)

theorem revisit_excluded (r : Bool → Bool → Prop) (hr : ∀ s a b, r s a → r s b → a = b) :
    ¬ Follows (fun _ => r) revisit := by
  intro hf
  have := functional_excludes r revisit 0 1 hr hf (by decide)
  exact absurd this (by decide)

theorem window_tf : UniqueSolution (FollowsFin onlyTF) (fun i : Fin 2 => decide (i = 0)) := by
  refine ⟨fun i => ?_, fun g hg => ?_⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact ⟨by decide, by decide⟩
  · have h := hg ⟨0, by omega⟩
    funext i
    match i with
    | ⟨0, _⟩ => exact h.1
    | ⟨1, _⟩ => exact h.2

theorem window_ft : UniqueSolution (FollowsFin onlyFT) (fun i : Fin 2 => decide (i = 1)) := by
  refine ⟨fun i => ?_, fun g hg => ?_⟩
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    exact ⟨by decide, by decide⟩
  · have h := hg ⟨0, by omega⟩
    funext i
    match i with
    | ⟨0, _⟩ => exact h.1
    | ⟨1, _⟩ => exact h.2

theorem controls : TruthCore.Explanation.PathRelocation.Controls := by
  refine ⟨⟨alt_follows, alt_changes, flip_autonomous, flip_cases, flip_dating, alt_shift_ne⟩,
    fun a => ⟨flip_law_fails a, token_determines _ a⟩,
    ⟨pinned_unique, alt_changes, pinned_not_invariant⟩,
    ⟨fun f hf t => hf (t + 1), ?_, fun ⟨_, ht⟩ => ht rfl, fun a => (law_only _ a _ _).mpr ?_⟩,
    ⟨stay_follows, rise_follows, ?_, by decide, branch_fails⟩,
    ⟨revisit_excluded, copy_unique revisit⟩,
    ⟨_, window_tf, by decide, _, window_ft, ?_⟩,
    ⟨⟨rfl, rfl⟩, fun _ _ => trivial, no_cycle alt, predecessor_edge alt⟩⟩
  · exact ⟨fun _ => rfl, fun g hg => funext hg⟩
  · intro g hg
    funext t
    rw [hg t, a.2 t]
  · intro t ht
    simp only [stayFalse, riseAtOne]
    symm
    simp
    omega
  · intro h
    exact absurd (congrFun h 0) (by decide)

end TruthCore.Results.Explanation.PathRelocation
