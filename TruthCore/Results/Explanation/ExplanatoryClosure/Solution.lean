import TruthCore.Explanation.ExplanatoryClosure
import TruthCore.Results.Explanation.CondensationSufficiency.Solution
import TruthCore.Results.Explanation.JointCooperation.Solution
namespace TruthCore.Results.Explanation.ExplanatoryClosure
open TruthCore.Explanation.ExplanatoryClosure
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic.Regress Relation
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.JointCooperation
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Results.Causality.DerivativeJointPower (trap_obstruction)
set_option autoImplicit false
set_option linter.constructorNameAsVariable false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section General
variable {B E G S : Type}

theorem graph_all (h : Groups E G) : (allMembers h).graph = h.graph := by
  cases h
  simp [allMembers, Groups.graph, Groups.members]

theorem full_joint {h : Groups E G} {Stop : E → Prop} (g : G) (ha : h.admitted g)
    (hm : ∀ e ∈ h.members g, FullSupply h Stop e) : FullSupply h Stop (h.effect g) :=
  Supply.joint (h := allMembers h) g ha hm

theorem full_closed (h : Groups E G) (Stop : E → Prop) (e : E) (hs : FullSupply h Stop e) :
    Closed h Stop e := by
  refine ⟨{x | FullSupply h Stop x}, hs, ?_⟩
  intro x hx
  change Supply (allMembers h) Stop x at hx
  cases hx with
  | intrinsic _ hi => exact Or.inl hi
  | joint g ha hm => exact Or.inr ⟨g, ha, rfl, fun y hy => hm y hy⟩

theorem full_supply (h : Groups E G) (Stop : E → Prop) (e : E) (hs : FullSupply h Stop e) :
    Supply h Stop e := by
  change Supply (allMembers h) Stop e at hs
  induction hs with
  | intrinsic e hi => exact Supply.intrinsic e hi
  | joint g ha _ ih => exact Supply.joint g ha fun y hy => ih y (Or.inl hy)

theorem supply_full (h : Groups E G) (Stop : E → Prop) (he : ∀ g, h.enablers g = ∅) (e : E)
    (hs : Supply h Stop e) : FullSupply h Stop e := by
  induction hs with
  | intrinsic e hi => exact Supply.intrinsic e hi
  | joint g ha _ ih =>
    refine full_joint g ha ?_
    rintro y (hy | hy)
    · exact ih y hy
    · rw [he g] at hy; exact hy.elim

theorem not_full_iff (h : Groups E G) (Stop : E → Prop) (e : E) :
    ¬ FullSupply h Stop e ↔ ∃ D, Trap (allMembers h) Stop D ∧ e ∈ D := by
  constructor
  · intro hn
    refine ⟨{x | ¬ FullSupply h Stop x}, ⟨?_, ?_⟩, hn⟩
    · intro x hx hi
      exact hx (Supply.intrinsic x hi)
    · intro g ha hd
      by_contra hc
      apply hd
      refine full_joint g ha fun y hy => ?_
      by_contra hy'
      exact hc ⟨y, hy, hy'⟩
  · rintro ⟨D, ht, he⟩
    exact trap_obstruction _ _ _ ht e he

/-- Each unfounded member has an unfounded member of its chosen record. -/
theorem step (h : Groups E G) {Stop : E → Prop} {A : Set E} (ha : Accounted h Stop A)
    {x : E} (hx : x ∈ A) (hn : ¬ FullSupply h Stop x) :
    ¬ Stop x ∧ ∃ y, y ∈ A ∧ ¬ FullSupply h Stop y ∧ h.graph.edge y x := by
  have hs : ¬ Stop x := fun hi => hn (Supply.intrinsic x hi)
  refine ⟨hs, ?_⟩
  rcases ha x hx with hi | ⟨g, hg, rfl, hm⟩
  · exact (hs hi).elim
  · by_contra hc
    apply hn
    refine full_joint g hg fun y hy => ?_
    by_contra hy'
    exact hc ⟨y, hm hy, hy', g, hg, rfl, hy⟩

theorem chain_trans {K : Graph E} (f : Nat → E) (he : ∀ n, K.edge (f (n + 1)) (f n)) (i k : Nat) :
    TransGen K.edge (f (i + k + 1)) (f i) := by
  induction k with
  | zero => exact TransGen.single (he i)
  | succ k ih => exact TransGen.head (he (i + k + 1)) ih

theorem unfounded_of (h : Groups E G) {Stop : E → Prop} {A : Set E} (ha : Accounted h Stop A)
    {t : E} (ht : t ∈ A) (hn : ¬ FullSupply h Stop t) : Unfounded h Stop A t := by
  classical
  let D := {x : E // x ∈ A ∧ ¬ FullSupply h Stop x}
  have hstep : ∀ x : D, ∃ y : D, h.graph.edge y.1 x.1 := fun x => by
    obtain ⟨_, y, hy, hyn, hye⟩ := step h ha x.2.1 x.2.2
    exact ⟨⟨y, hy, hyn⟩, hye⟩
  choose next hnext using hstep
  let w : Nat → D := fun n => Nat.rec ⟨t, ht, hn⟩ (fun _ x => next x) n
  have hw : ∀ n, h.graph.edge (w (n + 1)).1 (w n).1 := fun n => hnext (w n)
  refine ⟨fun n => (w n).1, rfl, fun n => ⟨(w n).2.1, ?_, (w n).2.2, hw n⟩, ?_⟩
  · exact (step h ha (w n).2.1 (w n).2.2).1
  · by_cases hi : Function.Injective fun n => (w n).1
    · exact Or.inr hi
    · left
      simp only [Function.Injective, not_forall] at hi
      obtain ⟨i, j, hij, hne⟩ := hi
      have hij' : (w i).1 = (w j).1 := hij
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · refine ⟨i, ?_⟩
        have := chain_trans (K := h.graph) (fun n => (w n).1) hw i (j - i - 1)
        have hj : i + (j - i - 1) + 1 = j := by omega
        simp only [hj] at this
        rw [← hij'] at this
        exact this
      · refine ⟨j, ?_⟩
        have := chain_trans (K := h.graph) (fun n => (w n).1) hw j (i - j - 1)
        have hj : j + (i - j - 1) + 1 = i := by omega
        simp only [hj] at this
        rw [hij'] at this
        exact this

theorem fork : Fork := by
  intro E G h Stop A t ha ht
  refine ⟨?_, ?_⟩
  · by_cases hf : FullSupply h Stop t
    · exact Or.inl hf
    · exact Or.inr (unfounded_of h ha ht hf)
  · rintro ⟨hf, f, h0, hn, _⟩
    exact (hn 0).2.2.1 (h0 ▸ hf)

theorem ladder : TruthCore.Explanation.ExplanatoryClosure.Ladder := by
  intro E G h Stop
  refine ⟨graph_all h, full_closed h Stop, full_supply h Stop, fun he e => supply_full h Stop he e,
    not_full_iff h Stop, ?_, ?_⟩
  · intro wf e ⟨A, he, ha⟩
    by_contra hn
    obtain ⟨f, _, hf, _⟩ := unfounded_of h ha he hn
    obtain ⟨_, ⟨n, rfl⟩, hmin⟩ := wf.has_min (Set.range f) ⟨_, 0, rfl⟩
    exact hmin (f (n + 1)) ⟨n + 1, rfl⟩ (hf n).2.2.2
  · intro hfin hnc e ⟨A, he, ha⟩
    by_contra hn
    obtain ⟨f, _, _, hc | hi⟩ := unfounded_of h ha he hn
    · obtain ⟨i, hi⟩ := hc
      exact hnc _ hi
    · exact not_injective_infinite_finite f hi

theorem contingent_iff (m : Exercise B E G S) (e : E) :
    Contingent (arena m) m.actual e ↔ m.occurs m.actual e ∧ ¬ NecessaryIn m e := by
  constructor
  · rintro ⟨ho, v, hv, hn⟩
    exact ⟨ho, fun hb => hn (hb v hv)⟩
  · rintro ⟨ho, hn⟩
    simp only [NecessaryIn, not_forall] at hn
    obtain ⟨v, hv, hnv⟩ := hn
    exact ⟨ho, v, hv, hnv⟩

theorem explains_iff (m : Exercise B E G S) (r f : E) :
    (arena m).explains m.actual r f ↔
      ∃ g, m.groups.admitted g ∧ m.exercised g ∧ m.groups.effect g = f ∧ r ∈ m.groups.members g :=
  ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩

theorem occurring_accounted (m : Exercise B E G S) (hc : m.coherent) (Stop : E → Prop)
    (hcov : ∀ e, m.occurs m.actual e → Stop e ∨ Explained (arena m) m.actual e) :
    Accounted m.exercisedGroups Stop {e | m.occurs m.actual e} := by
  intro e he
  rcases hcov e he with hs | ⟨r, hr⟩
  · exact Or.inl hs
  · obtain ⟨g, ha, hx, rfl, _⟩ := (explains_iff m r e).1 hr
    exact Or.inr ⟨g, ⟨ha, hx⟩, rfl, fun y hy => (hc.2 g hx).2.1 y hy⟩

theorem psr_closed (m : Exercise B E G S) (hc : m.coherent)
    (hp : ContingentPSR (arena m) m.actual) (e : E) (he : m.occurs m.actual e) :
    Closed m.exercisedGroups (NecessaryIn m) e := by
  classical
  refine ⟨_, he, occurring_accounted m hc _ fun x hx => ?_⟩
  by_cases hn : NecessaryIn m x
  · exact Or.inl hn
  · exact Or.inr (hp x ((contingent_iff m x).2 ⟨hx, hn⟩))

theorem collapse : Collapse := by
  intro B E G S m hc hne
  have hreason : ∀ (Stop : E → Prop) e, Closed m.exercisedGroups Stop e → ¬ Stop e →
      Explained (arena m) m.actual e := by
    rintro Stop e ⟨A, he, ha⟩ hs
    rcases ha e he with hi | ⟨g, ⟨hg, hx⟩, rfl, _⟩
    · exact (hs hi).elim
    · obtain ⟨r, hr⟩ := hne g hg hx
      exact ⟨r, (explains_iff m _ _).2 ⟨g, hg, hx, rfl, hr⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, psr_closed m hc⟩
  · intro hall e he
    exact hreason _ e (hall e he) ((contingent_iff m e).1 he).2
  · intro hp e he
    exact psr_closed m hc hp e ((contingent_iff m e).1 he).1
  · intro hall e he
    exact hreason _ e (hall e he) id
  · intro hp e he
    exact ⟨_, he, occurring_accounted m hc _ fun x hx => Or.inr (hp x hx)⟩

theorem total_target : TotalTarget := by
  rintro B E G S m t hnt hne htot ⟨A, ht, ha⟩ c hc
  have hcn := ((contingent_iff m c).1 hc).2
  have hrec : ∀ x ∈ A, ¬ NecessaryIn m x → Explained (arena m) m.actual x := by
    intro x hx hn
    rcases ha x hx with hi | ⟨g, ⟨hg, hex⟩, rfl, _⟩
    · exact (hn hi).elim
    · obtain ⟨r, hr⟩ := hne g hg hex
      exact ⟨r, (explains_iff m _ _).2 ⟨g, hg, hex, rfl, hr⟩⟩
  by_cases hct : c = t
  · subst hct; exact hrec c ht hcn
  · rcases ha t ht with hi | ⟨g, ⟨hg, hex⟩, he, hm⟩
    · exact (hnt hi).elim
    · exact hrec c (hm (htot g hg hex he c hc hct)) hcn

theorem reason_bridge : ReasonBridge := by
  intro B E G S m A x hr
  refine ⟨A, hr.explanandum, ?_⟩
  intro e he
  classical
  by_cases hn : NecessaryIn m e
  · exact Or.inl hn
  · right
    obtain ⟨r, hr'⟩ := hr.covered e he ((contingent_iff m e).2 ⟨hr.truthful e he, hn⟩)
    obtain ⟨g, hg, hex, rfl, _⟩ := (explains_iff m r _).1 hr'
    exact ⟨g, ⟨hg, hex⟩, rfl, fun y hy =>
      hr.closed y _ he ((explains_iff m _ _).2 ⟨g, hg, hex, rfl, hy⟩)⟩

theorem link_of_full (m : Exercise B E G S) (Stop : E → Prop) (hst : ∀ e, Stop e → NecessaryIn m e)
    (t : E) (hs : FullSupply m.exercisedGroups Stop t) (hn : ¬ NecessaryIn m t) :
    IncompleteLink m t := by
  classical
  change Supply (allMembers m.exercisedGroups) Stop t at hs
  induction hs with
  | intrinsic e hi => exact (hn (hst e hi)).elim
  | joint g ha hm ih =>
    obtain ⟨hg, hx⟩ := ha
    by_cases hall : ∀ y ∈ m.groups.members g, NecessaryIn m y
    · refine ⟨g, hg, hx, fun hsuff => hn fun s hal => hsuff s hal fun y hy => hall y hy s hal, .refl⟩
    · simp only [not_forall] at hall
      obtain ⟨y, hy, hyn⟩ := hall
      obtain ⟨g', hg', hx', hns, hp⟩ := ih y hy hyn
      exact ⟨g', hg', hx', hns, hp.tail ⟨g, ⟨hg, hx⟩, rfl, hy⟩⟩

theorem link_cost : LinkCost := by
  intro B E G S m Stop t hs hst
  refine ⟨link_of_full m Stop hst t hs, fun hall => ?_⟩
  by_contra hn
  obtain ⟨g, hg, hx, hns, _⟩ := link_of_full m Stop hst t hs hn
  exact hns (hall g hg hx)

theorem modal_cost : ModalCost := by
  intro B E G S W m o w Stop t hw hv hs hst hct
  have hb := TruthCore.Results.Explanation.JointCooperation.modal_bridges B E G S W m o w
  refine link_of_full m Stop (fun e he => hb.1 hw e (hst e he)) t hs fun hn => ?_
  obtain ⟨_, v, hacc, hnv⟩ := hct
  exact hnv (hb.2.1 hv t hn v hacc)

theorem occurs_of_anc (m : Exercise B E G S) (hc : m.coherent) {x t : E}
    (hp : ReflTransGen m.exercisedGroups.graph.edge x t) (ht : m.occurs m.actual t) :
    m.occurs m.actual x := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact ht
  | head he _ _ =>
    obtain ⟨g, ⟨_, hx⟩, _, hy⟩ := he
    exact (hc.2 g hx).2.1 _ hy

theorem brute_of_not_closed (m : Exercise B E G S) (hc : m.coherent) (t : E)
    (ho : m.occurs m.actual t) (hn : ¬ Closed m.exercisedGroups (NecessaryIn m) t) :
    BruteStop m t := by
  classical
  by_contra hb
  apply hn
  refine ⟨{x | ReflTransGen m.exercisedGroups.graph.edge x t}, ReflTransGen.refl, ?_⟩
  intro x hx
  by_cases hnx : NecessaryIn m x
  · exact Or.inl hnx
  · right
    by_contra hrec
    apply hb
    refine ⟨x, hx, (contingent_iff m x).2 ⟨occurs_of_anc m hc hx ho, hnx⟩, ?_⟩
    intro g hg hex he
    apply hrec
    refine ⟨g, ⟨hg, hex⟩, he, fun y hy => ?_⟩
    exact ReflTransGen.head ⟨g, ⟨hg, hex⟩, he, hy⟩ hx

theorem trilemma : Trilemma := by
  intro B E G S m t hc ht
  classical
  have ho := ((contingent_iff m t).1 ht).1
  have hnt := ((contingent_iff m t).1 ht).2
  by_cases hcl : Closed m.exercisedGroups (NecessaryIn m) t
  · obtain ⟨A, hA, ha⟩ := hcl
    by_cases hf : FullSupply m.exercisedGroups (NecessaryIn m) t
    · exact Or.inr (Or.inr (link_of_full m _ (fun _ h => h) t hf hnt))
    · exact Or.inr (Or.inl ⟨A, ha, unfounded_of _ ha hA hf⟩)
  · exact Or.inl (brute_of_not_closed m hc t ho hcl)

end General

/-! ## Family -/

abbrev FG (mo : Mode) := (family mo).exercisedGroups

theorem full_by {E G : Type} {h : Groups E G} {Stop : E → Prop} {e : E} (g : G)
    (he : h.effect g = e) (ha : h.admitted g) (hm : ∀ y ∈ h.members g, FullSupply h Stop y) :
    FullSupply h Stop e := he ▸ full_joint g ha hm

theorem family_coherent (mo : Mode) : (family mo).coherent := by
  refine ⟨trivial, fun g hg => ⟨hg, ?_, ?_⟩⟩
  · rintro y (hy | hy)
    · cases g with
      | dg => rcases hy with rfl | rfl | rfl <;> rfl
      | sa | sb | sc | sp => obtain rfl : y = .s := hy; trivial
      | qp => obtain rfl : y = .p := hy; rfl
      | pq => obtain rfl : y = .q := hy; exact ⟨hg, rfl⟩
      | lp => obtain rfl : y = .link 0 := hy; exact ⟨hg, rfl⟩
      | ll n => obtain rfl : y = .link (n + 1) := hy; exact ⟨hg, rfl⟩
    · cases g with
      | dg => obtain rfl : y = .p := hy; rfl
      | _ => cases hy
  · cases g with
    | dg => exact ⟨rfl, rfl, rfl, rfl⟩
    | sa | sb | sc | sp | pq | lp => rfl
    | qp | ll _ => exact ⟨hg, rfl⟩

theorem family_suff (mo : Mode) : (family mo).jointlySufficient .dg :=
  fun s _ hm => ⟨hm .a (Or.inl (Or.inl rfl)), hm .b (Or.inl (Or.inr (Or.inl rfl))),
    hm .c (Or.inl (Or.inr (Or.inr rfl))), hm .p (Or.inr rfl)⟩

theorem nn_p (mo : Mode) : ¬ NecessaryIn (family mo) .p := fun h => by
  have := h (true, true, true, false) trivial
  simp [family] at this

theorem nn_d (mo : Mode) : ¬ NecessaryIn (family mo) .d := fun h => by
  have := h (true, true, true, false) trivial
  simp [family] at this

theorem nn_q (mo : Mode) : ¬ NecessaryIn (family mo) .q := fun h => by
  have := h (true, true, true, false) trivial
  simp [family] at this

theorem nn_l (mo : Mode) (k : Nat) : ¬ NecessaryIn (family mo) (.link k) := fun h => by
  have := h (true, true, true, false) trivial
  simp [family] at this

theorem nec_s (mo : Mode) : NecessaryIn (family mo) .s := fun _ _ => trivial

theorem abc_full (mo : Mode) (x : Ev) (Stop : Ev → Prop) (hs : Stop .s)
    (g : Gp) (he : (family mo).groups.effect g = x) (hg : g = .sa ∨ g = .sb ∨ g = .sc) :
    FullSupply (FG mo) Stop x := by
  refine full_by (h := FG mo) g he ?_ ?_
  · rcases hg with rfl | rfl | rfl <;> exact ⟨trivial, trivial⟩
  · rintro y (hy | hy)
    · rcases hg with rfl | rfl | rfl <;> (subst hy; exact Supply.intrinsic _ hs)
    · rcases hg with rfl | rfl | rfl <;> cases hy

theorem d_full (mo : Mode) (Stop : Ev → Prop) (hs : Stop .s)
    (hp : FullSupply (FG mo) Stop .p) : FullSupply (FG mo) Stop .d := by
  refine full_by (h := FG mo) .dg rfl ⟨trivial, trivial⟩ ?_
  rintro y ((rfl | rfl | rfl) | rfl)
  · exact abc_full mo _ Stop hs .sa rfl (by simp)
  · exact abc_full mo _ Stop hs .sb rfl (by simp)
  · exact abc_full mo _ Stop hs .sc rfl (by simp)
  · exact hp

theorem bare_no_p (g : Gp) (ha : (family .bare).groups.admitted g) :
    (family .bare).groups.effect g ≠ .p := by
  cases g <;> simp [family, familyGroups] at ha ⊢

theorem bare_not_closed (Stop : Ev → Prop) (hd : ¬ Stop .d) (hp : ¬ Stop .p) :
    ¬ Closed (FG .bare) Stop .d := by
  rintro ⟨A, hA, ha⟩
  rcases ha .d hA with hi | ⟨g, hg, he, hm⟩
  · exact hd hi
  · cases g <;> first | cases he | skip
    have hpA : Ev.p ∈ A := hm (Or.inr rfl)
    rcases ha .p hpA with hi | ⟨g', hg', he', _⟩
    · exact hp hi
    · exact bare_no_p g' hg'.1 he'

theorem contingent_of (mo : Mode) (e : Ev) (ho : (family mo).occurs (family mo).actual e)
    (hn : ¬ NecessaryIn (family mo) e) :
    Contingent (arena (family mo)) (family mo).actual e := (contingent_iff _ e).2 ⟨ho, hn⟩

theorem psr_of (mo : Mode)
    (hP : Explained (arena (family mo)) (family mo).actual .p)
    (hQ : (family mo).occurs (family mo).actual .q → Explained (arena (family mo)) (family mo).actual .q)
    (hL : ∀ k, (family mo).occurs (family mo).actual (.link k) →
      Explained (arena (family mo)) (family mo).actual (.link k)) :
    ContingentPSR (arena (family mo)) (family mo).actual := by
  intro e he
  obtain ⟨ho, hn⟩ := (contingent_iff _ e).1 he
  cases e with
  | d => exact ⟨.a, rfl, .dg, trivial, trivial, rfl, Or.inl (Or.inl rfl)⟩
  | a => exact ⟨.s, rfl, .sa, trivial, trivial, rfl, Or.inl rfl⟩
  | b => exact ⟨.s, rfl, .sb, trivial, trivial, rfl, Or.inl rfl⟩
  | c => exact ⟨.s, rfl, .sc, trivial, trivial, rfl, Or.inl rfl⟩
  | p => exact hP
  | s => exact (hn (nec_s mo)).elim
  | q => exact hQ ho
  | link k => exact hL k ho

theorem psr_rooted : ContingentPSR (arena (family .rooted)) (family .rooted).actual :=
  psr_of _ ⟨.s, rfl, .sp, rfl, rfl, rfl, Or.inl rfl⟩ (fun h => by simp [family] at h)
    (fun _ h => by simp [family] at h)

theorem psr_cycle : ContingentPSR (arena (family .cycle)) (family .cycle).actual :=
  psr_of _ ⟨.q, rfl, .pq, rfl, rfl, rfl, Or.inl rfl⟩
    (fun _ => ⟨.p, rfl, .qp, rfl, rfl, rfl, Or.inl rfl⟩)
    (fun _ h => by simp [family] at h)

theorem psr_chain : ContingentPSR (arena (family .chain)) (family .chain).actual :=
  psr_of _ ⟨.link 0, rfl, .lp, rfl, rfl, rfl, Or.inl rfl⟩ (fun h => by simp [family] at h)
    (fun k _ => ⟨.link (k + 1), rfl, .ll k, rfl, rfl, rfl, Or.inl rfl⟩)

def isLoop : Ev → Prop
  | .d | .p | .q | .link _ => True
  | _ => False

theorem loop_not_full (mo : Mode) (hmo : mo = .chain ∨ mo = .cycle) :
    ¬ FullSupply (FG mo) (NecessaryIn (family mo)) .d := by
  refine (not_full_iff _ _ _).2 ⟨{e | isLoop e}, ⟨?_, ?_⟩, trivial⟩
  · intro e he hi
    cases e <;> first
      | exact he.elim
      | exact nn_d mo hi
      | exact nn_p mo hi
      | exact nn_q mo hi
      | exact nn_l mo _ hi
  · rintro g ⟨hg, _⟩ he
    cases g with
    | dg => exact ⟨.p, Or.inr rfl, trivial⟩
    | sa | sb | sc => exact he.elim
    | sp => rcases hmo with rfl | rfl <;> cases hg
    | qp => exact ⟨.p, Or.inl rfl, trivial⟩
    | pq => exact ⟨.q, Or.inl rfl, trivial⟩
    | lp => exact ⟨.link 0, Or.inl rfl, trivial⟩
    | ll n => exact ⟨.link (n + 1), Or.inl rfl, trivial⟩

open TruthCore.Explanation.CondensationSufficiency in
open TruthCore.Results.Explanation.CondensationSufficiency in
theorem cycle_comp : comp (familyGroups .cycle).graph .p = comp (familyGroups .cycle).graph .q :=
  (comp_eq_iff _ _ _).2 ⟨ReflTransGen.single ⟨.qp, rfl, rfl, Or.inl rfl⟩,
    ReflTransGen.single ⟨.pq, rfl, rfl, Or.inl rfl⟩⟩

open TruthCore.Explanation.CondensationSufficiency in
theorem cycle_condensed : Supply (condenseGroups (familyGroups .cycle)) (fun _ => False)
    (comp (familyGroups .cycle).graph .p) := by
  refine Supply.joint (h := condenseGroups (familyGroups .cycle)) (.pq : Gp) rfl ?_
  rintro y ⟨⟨z, hz, rfl⟩, hne⟩
  cases hz
  exact (hne cycle_comp.symm).elim

theorem cycle_no_reason (A : Ev → Prop) :
    ¬ TruthCore.Explanation.ExplanatoryAdequacy.ReasonClosed (arena (family .cycle)) (family .cycle).actual A .d := by
  intro hr
  have hp : A .p := hr.closed .p .d hr.explanandum ⟨rfl, .dg, trivial, trivial, rfl, Or.inr rfl⟩
  refine hr.nonCopy .q .p hp ⟨rfl, .pq, rfl, rfl, rfl, Or.inl rfl⟩
    (contingent_of _ _ rfl (nn_p _)) ?_
  intro v _
  simp [arena, family]

theorem shapes : Shapes := by
  refine ⟨fun mo => ⟨family_coherent mo, family_suff mo, ?_, ?_, ?_, ?_, nec_s mo, ?_, ?_⟩,
    ⟨?_, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, psr_rooted⟩, ?_, ⟨cycle_comp, cycle_condensed, cycle_no_reason⟩,
    ⟨?_, ?_⟩, ?_⟩
  · refine ⟨Or.inl rfl, fun hs => ?_⟩
    have := hs (false, true, true, true) trivial (by
      rintro y (⟨(rfl | rfl | rfl), hne⟩ | rfl)
      · exact (hne rfl).elim
      all_goals rfl)
    simp [family, familyGroups] at this
  · refine ⟨Or.inr (Or.inl rfl), fun hs => ?_⟩
    have := hs (true, false, true, true) trivial (by
      rintro y (⟨(rfl | rfl | rfl), hne⟩ | rfl)
      · rfl
      · exact (hne rfl).elim
      all_goals rfl)
    simp [family, familyGroups] at this
  · refine ⟨Or.inr (Or.inr rfl), fun hs => ?_⟩
    have := hs (true, true, false, true) trivial (by
      rintro y (⟨(rfl | rfl | rfl), hne⟩ | rfl)
      · rfl
      · rfl
      · exact (hne rfl).elim
      · rfl)
    simp [family, familyGroups] at this
  · refine ⟨Or.inr rfl, fun hs => ?_⟩
    have := hs (true, true, true, false) trivial (by
      rintro y ⟨(((rfl | rfl | rfl)) | rfl), hne⟩
      · rfl
      · rfl
      · rfl
      · exact (hne rfl).elim)
    simp [family, familyGroups] at this
  · have ha : ∀ g, g = Gp.sa ∨ g = Gp.sb ∨ g = Gp.sc →
        Supply (FG mo) (fun e => e = .s) ((FG mo).effect g) := by
      rintro g (rfl | rfl | rfl) <;>
      · exact Supply.joint _ ⟨trivial, trivial⟩ fun y hy => Supply.intrinsic y hy
    refine Supply.joint (h := FG mo) .dg ⟨trivial, trivial⟩ ?_
    rintro y (rfl | rfl | rfl)
    · exact ha .sa (by simp)
    · exact ha .sb (by simp)
    · exact ha .sc (by simp)
  · refine ⟨.sa, trivial, trivial, fun hs => ?_, ReflTransGen.single ⟨.dg, ⟨trivial, trivial⟩, rfl, Or.inl (Or.inl rfl)⟩⟩
    have := hs (false, true, true, true) trivial (by
      rintro y (rfl | hy)
      · trivial
      · cases hy)
    simp [family, familyGroups] at this
  · funext s e
    cases e <;> simp [family]
  · exact bare_not_closed _ (nn_d _) (nn_p _)
  · intro hf
    exact bare_not_closed (fun e => e = .s) (by simp) (by simp) (full_closed _ _ _ hf)
  · exact d_full _ _ (Or.inl (nec_s _)) (Supply.intrinsic _ (Or.inr rfl))
  · exact full_closed _ _ _ (abc_full _ _ _ (nec_s _) .sa rfl (by simp))
  · intro hp
    obtain ⟨r, _, g, hg, _, he, _⟩ := hp .p (contingent_of _ _ rfl (nn_p _))
    exact bare_no_p g hg he
  · refine ⟨.p, ReflTransGen.single ⟨.dg, ⟨trivial, trivial⟩, rfl, Or.inr rfl⟩,
      contingent_of _ _ rfl (nn_p _), fun g hg _ he => bare_no_p g hg he⟩
  · refine d_full _ _ (nec_s _) ?_
    refine full_by (h := FG .rooted) .sp rfl ⟨rfl, rfl⟩ ?_
    rintro y (rfl | hy)
    · exact Supply.intrinsic _ (nec_s _)
    · cases hy
  · rintro mo hmo
    have hp : ContingentPSR (arena (family mo)) (family mo).actual := by
      rcases hmo with rfl | rfl
      · exact psr_chain
      · exact psr_cycle
    exact ⟨psr_closed _ (family_coherent mo) hp .d (by simp [family]), loop_not_full mo hmo, hp⟩
  · refine ⟨{e | e = .d}, rfl, ?_⟩
    rintro e rfl
    left
    intro s hs
    subst hs
    simp [narrowBare, family]
  · rintro ⟨_, hns⟩
    apply hns
    intro s hs _
    subst hs
    simp [narrowBare, family, familyGroups]
  · rintro mo hmo g hg he k hk hne
    have hg' : g = .dg := by cases g <;> first | rfl | cases he
    subst hg'
    obtain ⟨ho, hn⟩ := (contingent_iff _ k).1 hk
    cases k with
    | d => exact (hne rfl).elim
    | a => exact Or.inl (Or.inl rfl)
    | b => exact Or.inl (Or.inr (Or.inl rfl))
    | c => exact Or.inl (Or.inr (Or.inr rfl))
    | p => exact Or.inr rfl
    | s => exact (hn (nec_s mo)).elim
    | q => rcases hmo with rfl | rfl <;> simp [family] at ho
    | link n => rcases hmo with rfl | rfl <;> simp [family] at ho

/-! ## Controls -/

abbrev CG (mo : CMode) := (ctl mo).exercisedGroups

theorem control_coherent (mo : CMode) : (ctl mo).coherent := by
  refine ⟨trivial, fun g hg => ⟨hg, ?_, ?_⟩⟩
  · rintro y (hy | hy)
    · cases g <;> (subst hy; first | trivial | rfl)
    · cases hy
  · cases g <;> rfl

theorem c_nn_t (mo : CMode) : ¬ NecessaryIn (ctl mo) .t := fun h => by
  have := h false trivial; simp [ctl] at this

theorem c_nn_p (mo : CMode) : ¬ NecessaryIn (ctl mo) .p := fun h => by
  have := h false trivial; simp [ctl] at this

theorem c_nn_q (mo : CMode) : ¬ NecessaryIn (ctl mo) .q := fun h => by
  have := h false trivial; simp [ctl] at this

theorem c_nn_l (mo : CMode) (k : Nat) : ¬ NecessaryIn (ctl mo) (.link k) := fun h => by
  have := h false trivial; simp [ctl] at this

theorem c_contingent (mo : CMode) : Contingent (arena (ctl mo)) (ctl mo).actual .t :=
  (contingent_iff _ _).2 ⟨rfl, c_nn_t mo⟩

theorem suff_all (mo : CMode) (hmo : mo ≠ .source) (g : CGp) (hg : (ctl mo).groups.admitted g) :
    (ctl mo).jointlySufficient g := by
  intro s _ hm
  cases g with
  | tn => exact (hmo hg).elim
  | tp => exact hm .p (Or.inl rfl)
  | pq => exact hm .q (Or.inl rfl)
  | qp => exact hm .p (Or.inl rfl)
  | pl => exact hm (.link 0) (Or.inl rfl)
  | ll k => exact hm (.link (k + 1)) (Or.inl rfl)

theorem no_incomplete (mo : CMode) (hmo : mo ≠ .source) : ¬ IncompleteLink (ctl mo) .t := by
  rintro ⟨g, hg, _, hns, _⟩
  exact hns (suff_all mo hmo g hg)

def loopSet (mo : CMode) : CEv → Prop
  | .t | .p => True
  | .q => mo = .cycle
  | .link _ => mo = .chain
  | .n => False

theorem loop_accounted (mo : CMode) (hmo : mo = .cycle ∨ mo = .chain) :
    Accounted (CG mo) (NecessaryIn (ctl mo)) {e | loopSet mo e} := by
  intro e he
  right
  rcases hmo with rfl | rfl
  · have hs : CMode.cycle ≠ .source := by decide
    cases e with
    | t => exact ⟨.tp, ⟨hs, hs⟩, rfl, by rintro y (rfl | hy); trivial; cases hy⟩
    | p => exact ⟨.pq, ⟨rfl, rfl⟩, rfl, by rintro y (rfl | hy); exact rfl; cases hy⟩
    | q => exact ⟨.qp, ⟨rfl, rfl⟩, rfl, by rintro y (rfl | hy); trivial; cases hy⟩
    | n => exact he.elim
    | link k => cases he
  · have hs : CMode.chain ≠ .source := by decide
    cases e with
    | t => exact ⟨.tp, ⟨hs, hs⟩, rfl, by rintro y (rfl | hy); trivial; cases hy⟩
    | p => exact ⟨.pl, ⟨rfl, rfl⟩, rfl, by rintro y (rfl | hy); exact rfl; cases hy⟩
    | link k => exact ⟨.ll k, ⟨rfl, rfl⟩, rfl, by rintro y (rfl | hy); exact rfl; cases hy⟩
    | n => exact he.elim
    | q => cases he

theorem loop_not_full_c (mo : CMode) (hmo : mo = .cycle ∨ mo = .chain) :
    ¬ FullSupply (CG mo) (NecessaryIn (ctl mo)) .t := by
  refine (not_full_iff _ _ _).2 ⟨{e | loopSet mo e}, ⟨?_, ?_⟩, trivial⟩
  · intro e he hi
    cases e with
    | t => exact c_nn_t mo hi
    | p => exact c_nn_p mo hi
    | q => exact c_nn_q mo hi
    | link k => exact c_nn_l mo k hi
    | n => exact he
  · rintro g ⟨hg, _⟩ he
    rcases hmo with rfl | rfl
    · cases g with
      | tp => exact ⟨.p, Or.inl rfl, trivial⟩
      | tn => cases hg
      | pq => exact ⟨.q, Or.inl rfl, rfl⟩
      | qp => exact ⟨.p, Or.inl rfl, trivial⟩
      | pl => cases hg
      | ll k => cases hg
    · cases g with
      | tp => exact ⟨.p, Or.inl rfl, trivial⟩
      | tn => cases hg
      | pq => cases hg
      | qp => cases hg
      | pl => exact ⟨.link 0, Or.inl rfl, rfl⟩
      | ll k => exact ⟨.link (k + 1), Or.inl rfl, rfl⟩

theorem has_record (mo : CMode) (hmo : mo = .cycle ∨ mo = .chain) {x y : CEv}
    (he : (CG mo).graph.edge x y) : ∃ g, (ctl mo).groups.admitted g ∧
      (ctl mo).exercised g ∧ (ctl mo).groups.effect g = x := by
  obtain ⟨g, ⟨hg, _⟩, _, hm⟩ := he
  rcases hmo with rfl | rfl
  · cases g with
    | tp => cases hm with
      | inl h => subst h; exact ⟨.pq, rfl, rfl, rfl⟩
      | inr h => cases h
    | tn => cases hg
    | pq => cases hm with
      | inl h => subst h; exact ⟨.qp, rfl, rfl, rfl⟩
      | inr h => cases h
    | qp => cases hm with
      | inl h => subst h; exact ⟨.pq, rfl, rfl, rfl⟩
      | inr h => cases h
    | pl => cases hg
    | ll k => cases hg
  · cases g with
    | tp => cases hm with
      | inl h => subst h; exact ⟨.pl, rfl, rfl, rfl⟩
      | inr h => cases h
    | tn => cases hg
    | pq => cases hg
    | qp => cases hg
    | pl => cases hm with
      | inl h => subst h; exact ⟨.ll 0, rfl, rfl, rfl⟩
      | inr h => cases h
    | ll k => cases hm with
      | inl h => subst h; exact ⟨.ll (k + 1), rfl, rfl, rfl⟩
      | inr h => cases h

theorem loop_no_brute (mo : CMode) (hmo : mo = .cycle ∨ mo = .chain) : ¬ BruteStop (ctl mo) .t := by
  rintro ⟨x, hp, _, hnr⟩
  rcases ReflTransGen.cases_head hp with rfl | ⟨c, he, _⟩
  · have hne : mo ≠ .source := by rcases hmo with rfl | rfl <;> decide
    exact hnr .tp hne hne rfl
  · obtain ⟨g, hg, hx, hef⟩ := has_record mo hmo he
    exact hnr g hg hx hef

def rank : CEv → Nat
  | .t | .q | .n => 0
  | .p => 1
  | .link k => k + 2

theorem chain_rank {x y : CEv} (he : (CG .chain).graph.edge x y) : rank y < rank x := by
  obtain ⟨g, ⟨hg, _⟩, hef, hm⟩ := he
  cases g with
  | tp => cases hm with
    | inl h => subst h; subst hef; simp [rank, ctl, controlGroups, CG, Exercise.exercisedGroups]
    | inr h => cases h
  | tn => cases hg
  | pq => cases hg
  | qp => cases hg
  | pl => cases hm with
    | inl h => subst h; subst hef; simp [rank, ctl, controlGroups, CG, Exercise.exercisedGroups]
    | inr h => cases h
  | ll k => cases hm with
    | inl h => subst h; subst hef; simp [rank, ctl, controlGroups, CG, Exercise.exercisedGroups]
    | inr h => cases h

theorem chain_noCycles : (CG .chain).graph.NoCycles := by
  intro x hx
  have : ∀ a b, TransGen (CG .chain).graph.edge a b → rank b < rank a := by
    intro a b h
    induction h with
    | single he => exact chain_rank he
    | tail _ he ih => exact lt_trans (chain_rank he) ih
  exact lt_irrefl _ (this x x hx)

theorem source_full : FullSupply (CG .source) (NecessaryIn (ctl .source)) .t := by
  refine full_by (h := CG .source) .tn rfl ⟨rfl, rfl⟩ ?_
  rintro y (rfl | hy)
  · exact Supply.intrinsic _ fun _ _ => trivial
  · cases hy

theorem trilemma_controls : TrilemmaControls := by
  refine ⟨fun mo => ⟨control_coherent mo, c_contingent mo⟩, ⟨?_, ?_, no_incomplete _ (by decide), ?_, c_nn_p _⟩,
    ⟨?_, ?_, ?_, source_full⟩, ?_, ⟨.qp, ⟨rfl, rfl⟩, rfl, Or.inl rfl⟩, ⟨.pq, ⟨rfl, rfl⟩, rfl, Or.inl rfl⟩,
    chain_noCycles, ⟨?_, ?_, ?_⟩⟩
  · have hs : CMode.brute ≠ .source := by decide
    refine ⟨.p, ReflTransGen.single ⟨.tp, ⟨hs, hs⟩, rfl, Or.inl rfl⟩,
      (contingent_iff _ _).2 ⟨rfl, c_nn_p _⟩, ?_⟩
    intro g hg _ he
    cases g <;> first | (cases he; done) | (cases hg; done)
  · rintro A ⟨f, h0, hf, _⟩
    have h1 := (hf 0).2.2.2
    rw [h0] at h1
    obtain ⟨g, ⟨hg, _⟩, he, hm⟩ := h1
    cases g with
    | tp =>
      have hy : f 1 = .p := by rcases hm with h | h; exact h; cases h
      have h2 := (hf 1).2.2.2
      rw [hy] at h2
      obtain ⟨g', ⟨hg', _⟩, he', _⟩ := h2
      cases g' <;> first | (cases he'; done) | (cases hg'; done)
    | tn => exact absurd hg (show ¬ (CMode.brute = .source) by decide)
    | pq | qp | pl | ll _ => cases he
  · have hs : CMode.brute ≠ .source := by decide
    refine full_by (h := CG .brute) .tp rfl ⟨hs, hs⟩ ?_
    rintro y (rfl | hy)
    · exact Supply.intrinsic _ rfl
    · cases hy
  · rintro ⟨x, hp, hc, hnr⟩
    rcases ReflTransGen.cases_head hp with rfl | ⟨c, he, _⟩
    · exact hnr .tn rfl rfl rfl
    · obtain ⟨g, ⟨hg, _⟩, _, hm⟩ := he
      cases g with
      | tp => exact (hg rfl).elim
      | pq | qp | pl | ll _ => cases hg
      | tn =>
        rcases hm with h | h
        · subst h
          exact ((contingent_iff _ _).1 hc).2 fun _ _ => trivial
        · cases h
  · rintro A ⟨f, h0, hf, _⟩
    exact (hf 0).2.2.1 (h0 ▸ source_full)
  · refine ⟨.tn, rfl, rfl, fun hs => ?_, .refl⟩
    have := hs false trivial (by
      rintro y (rfl | hy)
      · trivial
      · cases hy)
    simp [ctl, controlGroups] at this
  · intro mo hmo
    have hne : mo ≠ .source := by rcases hmo with rfl | rfl <;> decide
    have hac := loop_accounted mo hmo
    have hnf := loop_not_full_c mo hmo
    have htm : CEv.t ∈ {e | loopSet mo e} := trivial
    exact ⟨loop_no_brute mo hmo, no_incomplete mo hne, ⟨_, htm, hac⟩, hnf,
      ⟨_, hac, unfounded_of _ hac htm hnf⟩⟩
  · refine full_by (h := narrowSource.exercisedGroups) .tn rfl ⟨rfl, rfl⟩ ?_
    rintro y (rfl | hy)
    · exact Supply.intrinsic _ fun _ _ => trivial
    · cases hy
  · intro g hg _
    cases g with
    | tn => intro s hs _; exact hs
    | tp => exact (hg rfl).elim
    | pq | qp | pl | ll _ => cases hg
  · intro s hs; exact hs

/-! ## Lens and premise controls -/

theorem lens : IndispensableLens := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro B E G S m g e hs hn ⟨_, hns⟩
    classical
    refine hns fun s hal ho => hs s hal fun y hy => ?_
    by_cases hye : y = e
    · subst hye; exact hn s hal
    · exact ho y ⟨hy, hye⟩
  · intro B E G S m g e hc hen
    have hset : (m.groups.contributors g \ {e}) ∪ m.groups.enablers g = m.groups.members g \ {e} := by
      ext y
      constructor
      · rintro (⟨a, b⟩ | a)
        · exact ⟨Or.inl a, b⟩
        · exact ⟨Or.inr a, fun hy => hen (hy ▸ a)⟩
      · rintro ⟨a | a, b⟩
        · exact Or.inl ⟨a, b⟩
        · exact Or.inr a
    unfold Exercise.indispensable IndispensableCondition
    rw [hset]
    exact ⟨fun h => ⟨Or.inl h.1, h.2⟩, fun h => ⟨hc, h.2⟩⟩
  · rintro B E G S m Stop e ⟨A, he, ha⟩
    refine ⟨A, he, fun x hx => ?_⟩
    rcases ha x hx with hs | ⟨g, ⟨hg, hex⟩, hf, hm⟩
    · exact Or.inl hs
    · exact Or.inr ⟨g, hg, hex, hf, fun y hy => hm hy.1⟩
  · refine ⟨⟨trivial, fun g _ => ⟨trivial, ?_, ?_⟩⟩, ?_, ?_, ?_⟩
    · rintro y (hy | hy)
      · cases y <;> first | rfl | exact hy.elim
      · cases hy
    · exact Or.inl rfl
    · intro s _ hm
      exact Or.inl (hm .x (Or.inl trivial))
    · refine ⟨{e | e = .z}, rfl, ?_⟩
      rintro x rfl
      refine Or.inr ⟨(), trivial, trivial, rfl, ?_⟩
      rintro y ⟨_, hns⟩
      exfalso
      apply hns
      cases y with
      | x => intro s _ hm; exact Or.inr (hm .y ⟨Or.inl trivial, by simp⟩)
      | y => intro s _ hm; exact Or.inl (hm .x ⟨Or.inl trivial, by simp⟩)
      | z => intro s _ hm; exact Or.inl (hm .x ⟨Or.inl trivial, by simp⟩)
    · rintro ⟨A, hA, ha⟩
      rcases ha .z hA with hn | ⟨_, _, _, hm⟩
      · have := hn (false, false) trivial
        simp [backup] at this
      · have hx : OEv.x ∈ A := hm (Or.inl trivial)
        rcases ha .x hx with hn | ⟨_, _, he, _⟩
        · have := hn (false, false) trivial
          simp [backup] at this
        · cases he

theorem premise_controls : PremiseControls := by
  refine ⟨⟨⟨trivial, fun _ _ => ⟨trivial, ?_, rfl⟩⟩, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rintro y (hy | hy) <;> cases hy
  · rintro _ _
    refine ⟨Set.univ, trivial, fun _ _ => Or.inr ⟨(), ⟨trivial, trivial⟩, rfl, ?_⟩⟩
    rintro y (hy | hy) <;> cases hy
  · intro hp
    obtain ⟨r, _, _, _, _, _, hm⟩ := hp () ⟨rfl, false, trivial, by simp [arena, emptyExercise]⟩
    rcases hm with hy | hy <;> cases hy
  · intro hc
    have := (hc.2 () trivial).2.1 false (Or.inl rfl)
    simp [incoherentExercise] at this
  · intro _ _ _
    exact ⟨false, Or.inl rfl⟩
  · rintro e ⟨ho, _⟩
    have he : e = true := ho.1
    subst he
    exact ⟨false, rfl, (), trivial, trivial, rfl, Or.inl rfl⟩
  · exact ⟨⟨rfl, rfl⟩, false, trivial, by simp [arena, incoherentExercise]⟩
  · rintro ⟨A, hA, ha⟩
    rcases ha true hA with hn | ⟨_, _, _, hm⟩
    · have := hn false trivial
      simp [incoherentExercise] at this
    · have hf : false ∈ A := hm (Or.inl rfl)
      rcases ha false hf with hn | ⟨_, _, he, _⟩
      · have := hn true trivial
        simp [incoherentExercise] at this
      · cases he

theorem certificate : TruthCore.Explanation.ExplanatoryClosure.Certificate :=
  ⟨ladder, fork, collapse, total_target, reason_bridge, trilemma, link_cost, modal_cost,
    shapes, trilemma_controls, lens, premise_controls⟩

end TruthCore.Results.Explanation.ExplanatoryClosure
