import TruthCore.Explanation.CondensationSufficiency
import TruthCore.Results.Causality.DerivativeJointPower.Solution
import TruthCore.Results.Causality.CompleteCauseSourceUniqueness.Solution
import TruthCore.Results.Explanation.UltimateAdequacy.Solution
import Mathlib.Order.WellFoundedSet
namespace TruthCore.Results.Explanation.CondensationSufficiency
open TruthCore.Logic.Regress Relation
open TruthCore.Causality.JointGroups
open TruthCore.Causality.DerivativeJointPower
open TruthCore.Explanation.CondensationSufficiency
open TruthCore.Explanation.PSRStrength
open TruthCore.Results.Causality.DerivativeJointPower (trap_obstruction escape_iff local_rooted rooted_control source_free_control)
variable {E G : Type}

/-- The group-sensitive AND/OR operator computes EXACTLY the inductive Supply
standard. Unlike the ordinary graph projection, it retains which
contributions must work together. The least fixed point handles cycles and
does not presume finite derivation depth when groups are infinite. -/
theorem support_eq_lfp (h : Groups E G) (S : Set E) :
    {e | Supply h (fun x => x ∈ S) e} = (supportStep h S).lfp := by
  apply le_antisymm
  · intro e hs
    induction hs with
    | intrinsic e hi =>
      rw [← (supportStep h S).map_lfp]
      exact Or.inl hi
    | joint g hg _ ih =>
      rw [← (supportStep h S).map_lfp]
      exact Or.inr ⟨g, hg, rfl, fun a ha => ih a ha⟩
  · apply (supportStep h S).lfp_le
    intro e he
    rcases he with hs | ⟨g, hg, he, hAll⟩
    · exact .intrinsic e hs
    · subst e
      exact .joint g hg (fun a ha => hAll a ha)

/-- Increasing the intrinsic input set cannot remove a derived supply
certificate. A record's contributor family is never collapsed to one edge. -/
theorem support_mono (h : Groups E G) {S T : Set E} {e : E}
    (hST : S ⊆ T) (hs : Supply h (fun x => x ∈ S) e) :
    Supply h (fun x => x ∈ T) e := by
  induction hs with
  | intrinsic e hi => exact .intrinsic e (hST hi)
  | joint g hg _ ih => exact .joint g hg (fun a ha => ih a ha)

/-- With nonempty contributor sets, no effect has inductive Supply from an
empty intrinsic input. Empty productive records would invalidate this. -/
theorem no_empty_support (h : Groups E G)
    (hNonempty : ∀ g, h.admitted g → (h.contributors g).Nonempty)
    (e : E) : ¬ Supply h (fun x => x ∈ (∅ : Set E)) e := by
  intro hs
  induction hs with
  | intrinsic e hi => exact hi
  | joint g hg _ ih =>
    obtain ⟨a, ha⟩ := hNonempty g hg
    exact ih a ha

/-- Inclusion-minimal intrinsic support sets form an antichain. This does NOT
say the family has one member or that every target has a support. -/
theorem minimal_support_antichain (h : Groups E G) (I : E → Prop) (e : E)
    {S T : Set E} (hS : MinimalIntrinsicSupport h I S e)
    (hT : MinimalIntrinsicSupport h I T e)
    (hST : S ⊆ T) : S = T :=
  Set.Subset.antisymm hST (hT.2 S hS.1 hST)

/-- A supplied singleton is minimal if there is no empty-group production.
No claim is made that it is the only minimal support when other intrinsic
contributors are available. -/
theorem singleton_minimal (h : Groups E G) (I : E → Prop) (s e : E)
    (his : I s)
    (hNonempty : ∀ g, h.admitted g → (h.contributors g).Nonempty)
    (hs : Supply h (fun x => x ∈ ({s} : Set E)) e) :
    MinimalIntrinsicSupport h I {s} e := by
  refine ⟨⟨?_, hs⟩, ?_⟩
  · intro x hx
    have hxs : x = s := hx
    subst x
    exact his
  · intro T hT hTS
    have hsT : s ∈ T := by
      by_contra hNoS
      have hEmpty : T = ∅ := by
        ext x
        constructor
        · intro hx
          have hxs : x = s := hTS hx
          subst x
          exact (hNoS hx).elim
        · intro hx
          exact hx.elim
      have hNo : ¬ Supply h (fun x => x ∈ T) e := by
        simpa [hEmpty] using no_empty_support h hNonempty e
      exact hNo hT.2
    intro x hx
    have hxs : x = s := hx
    subst x
    exact hsT

/-- If the singleton exhausts the allowed intrinsic inputs, then it is the
only adequate intrinsic support set, not merely one minimal alternative. -/
theorem singleton_support_unique (h : Groups E G) (I : E → Prop)
    (s e : E) (hOnly : ∀ x, I x → x = s)
    (hMin : MinimalIntrinsicSupport h I {s} e)
    (T : Set E) (hT : IntrinsicSupport h I T e) : T = {s} := by
  have hSub : T ⊆ {s} := by
    intro x hx
    exact hOnly x (hT.1 hx)
  exact Set.Subset.antisymm hSub (hMin.2 T hT hSub)

/-- If every production record for an effect requires a contributor which
cannot itself be produced by any admitted record, that contributor must be
in every sufficient intrinsic seed set (unless the effect is seeded directly).
This is a group-level AND condition, not an edge-graph path claim. -/
theorem required_unproduced_seed (h : Groups E G) (S : Set E) (e a : E)
    (hNoTarget : e ∉ S)
    (hRequired : ∀ g, h.admitted g → h.effect g = e → a ∈ h.contributors g)
    (hUnproduced : ∀ g, h.admitted g → h.effect g ≠ a)
    (hs : Supply h (fun x => x ∈ S) e) : a ∈ S := by
  cases hs with
  | intrinsic _ he => exact (hNoTarget he).elim
  | joint g hg hAll =>
    have ha : a ∈ h.contributors g := hRequired g hg rfl
    have hSupplyA := hAll a ha
    cases hSupplyA with
    | intrinsic _ he => exact he
    | joint g hg _ => exact (hUnproduced g hg rfl).elim

theorem rtg_of_path {K : Graph E} {a b : E} (p : @Quiver.Path E (quiverOf K) a b) :
    ReflTransGen K.edge a b := by
  induction p with
  | nil => exact .refl
  | cons _ e ih => exact ih.tail e.down

theorem path_of_rtg {K : Graph E} {a b : E} (p : ReflTransGen K.edge a b) :
    Nonempty (@Quiver.Path E (quiverOf K) a b) := by
  let _ := quiverOf K
  induction p with
  | refl => exact ⟨.nil⟩
  | tail _ e ih => exact ⟨ih.some.cons ⟨e⟩⟩

theorem comp_eq_iff (K : Graph E) (a b : E) :
    comp K a = comp K b ↔ ReflTransGen K.edge a b ∧ ReflTransGen K.edge b a := by
  unfold comp
  let _ := quiverOf K
  rw [Quiver.StronglyConnectedComponent.mk_eq_mk]
  exact ⟨fun ⟨⟨p⟩, ⟨q⟩⟩ => ⟨rtg_of_path p, rtg_of_path q⟩,
    fun ⟨p, q⟩ => ⟨path_of_rtg p, path_of_rtg q⟩⟩

theorem comp_surj (K : Graph E) (C : Comp K) : ∃ e, comp K e = C := by
  let _ := quiverOf K
  exact Quotient.exists_rep C

theorem edge_cases (K : Graph E) {y x : E} (e : K.edge y x) :
    comp K y = comp K x ∨ (condensed K).edge (comp K y) (comp K x) := by
  by_cases h : comp K y = comp K x
  · exact Or.inl h
  · exact Or.inr ⟨h, y, x, rfl, rfl, e⟩

theorem condensed_rtg_of (K : Graph E) {y x : E} (p : ReflTransGen K.edge y x) :
    ReflTransGen (condensed K).edge (comp K y) (comp K x) := by
  induction p with
  | refl => exact .refl
  | tail _ e ih =>
    rcases edge_cases K e with h | h
    · rwa [← h]
    · exact ih.tail h

theorem rtg_of_condensed (K : Graph E) (y : E) {C : Comp K}
    (p : ReflTransGen (condensed K).edge (comp K y) C) :
    ∀ x, comp K x = C → ReflTransGen K.edge y x := by
  induction p with
  | refl => exact fun x hx => ((comp_eq_iff K x y).1 hx).2
  | tail _ e ih =>
    intro x hx
    obtain ⟨_, y', x', hy, hxx, he⟩ := e
    exact ((ih y' hy).tail he).trans ((comp_eq_iff K x' x).1 (hxx.trans hx.symm)).1

theorem condensed_noCycles (K : Graph E) : (condensed K).NoCycles := by
  intro A hA
  obtain ⟨B, ⟨hne, y, x, hy, hx, he⟩, hb⟩ := TransGen.head'_iff.1 hA
  subst hy hx
  have back := rtg_of_condensed K x hb y rfl
  exact hne ((comp_eq_iff K y x).2 ⟨.single he, back⟩)

theorem wcc_eq_iff (K : Graph E) (a b : E) : wcc K a = wcc K b ↔ EqvGen K.edge a b := by
  let _ := quiverOf K
  constructor
  · intro h
    obtain ⟨p⟩ := (Quiver.WeaklyConnectedComponent.eq a b).1 h
    clear h
    induction p with
    | nil => exact .refl _
    | cons _ e ih =>
      rcases e with e | e
      · exact ih.trans _ _ _ (.rel _ _ e.down)
      · exact ih.trans _ _ _ (.symm _ _ (.rel _ _ e.down))
  · intro h
    induction h with
    | rel _ _ e =>
      exact (Quiver.WeaklyConnectedComponent.eq _ _).2
        ⟨(Quiver.Path.nil).cons (Sum.inl ⟨e⟩)⟩
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ i j => exact i.trans j

theorem eqv_of_rtg (K : Graph E) {a b : E} (p : ReflTransGen K.edge a b) : EqvGen K.edge a b := by
  induction p with
  | refl => exact .refl _
  | tail _ e ih => exact .trans _ _ _ ih (.rel _ _ e)

theorem condensed_eqv_of (K : Graph E) {y x : E} (p : EqvGen K.edge y x) :
    EqvGen (condensed K).edge (comp K y) (comp K x) := by
  induction p with
  | rel _ _ e =>
    rcases edge_cases K e with h | h
    · rw [h]; exact .refl _
    · exact .rel _ _ h
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ i j => exact .trans _ _ _ i j

theorem eqv_of_condensed (K : Graph E) {A C : Comp K} (p : EqvGen (condensed K).edge A C) :
    ∀ y x, comp K y = A → comp K x = C → EqvGen K.edge y x := by
  induction p with
  | rel _ _ e =>
    intro y x hy hx
    obtain ⟨_, y', x', hy', hx', he⟩ := e
    exact .trans _ _ _ (eqv_of_rtg K ((comp_eq_iff K y y').1 (hy.trans hy'.symm)).1)
      (.trans _ _ _ (.rel _ _ he) (eqv_of_rtg K ((comp_eq_iff K x' x).1 (hx'.trans hx.symm)).1))
  | refl =>
    intro y x hy hx
    exact eqv_of_rtg K ((comp_eq_iff K y x).1 (hy.trans hx.symm)).1
  | symm _ _ _ ih =>
    intro y x hy hx
    exact .symm _ _ (ih x y hx hy)
  | trans _ B _ _ _ i j =>
    intro y x hy hx
    obtain ⟨m, hm⟩ := comp_surj K B
    exact .trans _ _ _ (i y m hy hm) (j m x hm hx)

theorem wcc_preserved (K : Graph E) (y x : E) :
    wcc K y = wcc K x ↔ wcc (condensed K) (comp K y) = wcc (condensed K) (comp K x) := by
  rw [wcc_eq_iff, wcc_eq_iff]
  exact ⟨condensed_eqv_of K, fun h => eqv_of_condensed K h y x rfl rfl⟩

theorem least_preserved (K : Graph E) (s : E) : least K s ↔ least (condensed K) (comp K s) := by
  constructor
  · intro h C
    obtain ⟨x, rfl⟩ := comp_surj K C
    exact condensed_rtg_of K (h x)
  · intro h x
    exact rtg_of_condensed K s (h (comp K x)) x rfl

theorem source_preserved (K : Graph E) (s : E) (hs : K.Source s) :
    (condensed K).Source (comp K s) := by
  rintro ⟨A, hne, y, x, hy, hx, he⟩
  have back := ((comp_eq_iff K s x).1 hx.symm).2
  have : s = x := by
    cases ReflTransGen.cases_tail back with
    | inl h => exact h
    | inr h =>
      obtain ⟨c, _, hc⟩ := h
      exact (hs ⟨c, hc⟩).elim
  subst this
  exact (hs ⟨y, he⟩).elim

theorem finite_wf (K : Graph E) [Finite E] : WellFounded (condensed K).edge := by
  let _ := quiverOf K
  have : Finite (Comp K) := Quotient.finite _
  have : Std.Irrefl (TransGen (condensed K).edge) := ⟨condensed_noCycles K⟩
  exact (Finite.wellFounded_of_trans_of_irrefl (TransGen (condensed K).edge)).mono
    (fun _ _ h => .single h)

theorem condense_graph (h : Groups E G) : (condenseGroups h).graph = condensed h.graph := by
  have : (condenseGroups h).graph.edge = (condensed h.graph).edge := by
    funext A C
    apply propext
    constructor
    · rintro ⟨g, hg, rfl, ⟨⟨a, ha, rfl⟩, hne⟩ | ⟨⟨a, ha, rfl⟩, hne⟩⟩
      · exact ⟨hne, a, h.effect g, rfl, rfl, g, hg, rfl, Or.inl ha⟩
      · exact ⟨hne, a, h.effect g, rfl, rfl, g, hg, rfl, Or.inr ha⟩
    · rintro ⟨hne, y, x, rfl, rfl, g, hg, rfl, hm | hm⟩
      · exact ⟨g, hg, rfl, Or.inl ⟨⟨y, hm, rfl⟩, hne⟩⟩
      · exact ⟨g, hg, rfl, Or.inr ⟨⟨y, hm, rfl⟩, hne⟩⟩
  cases hk : (condenseGroups h).graph
  cases hl : condensed h.graph
  simp_all

theorem graph_invariants : GraphInvariants :=
  ⟨fun _ K => condensed_noCycles K,
   fun _ K _ _ => ⟨condensed_rtg_of K, fun h => rtg_of_condensed K _ h _ rfl⟩,
   fun _ K y x => wcc_preserved K y x,
   fun _ K s => least_preserved K s,
   fun _ K s hs => source_preserved K s hs,
   fun _ hf K => by have := hf; exact finite_wf K,
   fun _ _ h => condense_graph h⟩

theorem supply_forward (h : Groups E G) (I : E → Prop) (e : E) (hs : Supply h I e) :
    Supply (condenseGroups h) (condensedIntrinsic h.graph I) (comp h.graph e) := by
  induction hs with
  | intrinsic e hi => exact .intrinsic _ ⟨e, rfl, hi⟩
  | joint g hg _ ih =>
    refine Supply.joint (h := condenseGroups h) g hg ?_
    rintro _ ⟨⟨a, ha, rfl⟩, _⟩
    exact ih a ha

theorem escape_of_component (h : Groups E G) (I A : E → Prop)
    (wf : WellFounded (condensed h.graph).edge) (ce : ComponentEscape h I A) : Escape h I A := by
  intro D hD hn
  let S : Set (Comp h.graph) := comp h.graph '' D
  obtain ⟨C, ⟨d, hd, rfl⟩, hmin⟩ := wf.has_min S (hn.image _)
  let D' : Set E := {e | e ∈ D ∧ comp h.graph e = comp h.graph d}
  rcases ce (comp h.graph d) D' (fun e he => ⟨hD he.1, he.2⟩) ⟨d, hd, rfl⟩ with
    ⟨e, he, hi⟩ | ⟨g, hg, hef, hm⟩
  · exact Or.inl ⟨e, he.1, hi⟩
  · refine Or.inr ⟨g, hg, hef.1, fun e he heD => ?_⟩
    by_cases hc : comp h.graph e = comp h.graph d
    · exact hm e he ⟨heD, hc⟩
    · exact hmin (comp h.graph e) ⟨e, heD, rfl⟩
        ⟨hc, e, h.effect g, rfl, hef.2, g, hg, rfl, Or.inl he⟩

theorem component_of_escape (h : Groups E G) (I A : E → Prop) (ee : Escape h I A) :
    ComponentEscape h I A :=
  fun _ D hD hn => ee D (fun _ he => (hD he).1) hn

theorem supply_iff_component (h : Groups E G) (I A : E → Prop) (hl : LocalPower h I A)
    (hc : PoweredGroups h A) (wf : WellFounded (condensed h.graph).edge) :
    (∀ e, A e → Supply h I e) ↔ ComponentEscape h I A :=
  (escape_iff h I A hl hc).trans
    ⟨component_of_escape h I A, escape_of_component h I A wf⟩

/-- Singleton components with a self-free supplier give component escape. -/
theorem component_of_singletons (h : Groups E G) (I A : E → Prop)
    (inj : ∀ a b, comp h.graph a = comp h.graph b → a = b)
    (rec : ∀ e, A e → I e ∨ ∃ g, h.admitted g ∧ h.effect g = e ∧ e ∉ h.contributors g) :
    ComponentEscape h I A := by
  rintro C D hD ⟨d, hd⟩
  have only : ∀ x ∈ D, x = d := fun x hx => inj _ _ ((hD hx).2.trans (hD hd).2.symm)
  rcases rec d (hD hd).1 with hi | ⟨g, hg, he, hm⟩
  · exact Or.inl ⟨d, hd, hi⟩
  · refine Or.inr ⟨g, hg, he ▸ hd, fun e heg heD => hm ?_⟩
    rwa [only e heD] at heg

theorem comp_inj_of_noCycles (K : Graph E) (hc : K.NoCycles) (a b : E)
    (h : comp K a = comp K b) : a = b := by
  obtain ⟨p, q⟩ := (comp_eq_iff K a b).1 h
  cases ReflTransGen.cases_head p with
  | inl h => exact h
  | inr h =>
    obtain ⟨c, hac, hc'⟩ := h
    exact (hc a ((TransGen.head'_iff.2 ⟨c, hac, hc'.trans q⟩))).elim

theorem acyclic_component (h : Groups E G) (I A : E → Prop) (hl : LocalPower h I A)
    (hc : h.graph.NoCycles) : ComponentEscape h I A := by
  refine component_of_singletons h I A (comp_inj_of_noCycles _ hc) ?_
  intro e he
  rcases (hl e).1 he with hi | ⟨g, hg, hef, _⟩
  · exact Or.inl hi
  · refine Or.inr ⟨g, hg, hef, fun hm => hc e (.single ⟨g, hg, hef, Or.inl hm⟩)⟩

theorem wf_supply (h : Groups E G) (I A : E → Prop) (hl : LocalPower h I A)
    (wf : WellFounded h.graph.edge) : ∀ e, A e → Supply h I e := by
  intro e
  induction e using wf.induction with
  | _ e ih =>
    intro he
    rcases (hl e).1 he with hi | ⟨g, hg, rfl, hm⟩
    · exact .intrinsic e hi
    · exact .joint g hg fun a ha => ih a ⟨g, hg, rfl, Or.inl ha⟩ (hm a ha)

theorem cut_trap (h : Groups E G) (I : E → Prop) (D : Set E)
    (hn : ∀ g, h.admitted g → (h.contributors g).Nonempty)
    (hc : GraphCut h.graph I D) : Trap h I D := by
  refine ⟨hc.1, fun g hg hd => ?_⟩
  obtain ⟨a, ha⟩ := hn g hg
  exact ⟨a, ha, hc.2 a _ hd ⟨g, hg, rfl, Or.inl ha⟩⟩

theorem supply_schema : SupplySchema :=
  ⟨fun _ _ h I e hs => supply_forward h I e hs,
   fun _ _ h I A wf => ⟨component_of_escape h I A, escape_of_component h I A wf⟩,
   fun _ _ h I A hl hc wf => supply_iff_component h I A hl hc wf,
   fun _ _ hf h I A hl hc => by
     have := hf
     exact supply_iff_component h I A hl hc (finite_wf h.graph),
   fun _ _ h I A hl hc => acyclic_component h I A hl hc,
   fun _ _ h I A hl wf => wf_supply h I A hl wf,
   fun _ _ h I D hn hc => cut_trap h I D hn hc⟩

theorem not_wf_of_chain (K : Graph E) (f : Nat → E) (he : ∀ n, K.edge (f (n + 1)) (f n))
    (hne : ∀ n, comp K (f (n + 1)) ≠ comp K (f n)) : ¬ WellFounded (condensed K).edge := by
  intro wf
  obtain ⟨_, ⟨n, rfl⟩, hmin⟩ := wf.has_min (Set.range fun n => comp K (f n)) ⟨_, 0, rfl⟩
  exact hmin (comp K (f (n + 1))) ⟨n + 1, rfl⟩ ⟨hne n, _, _, rfl, rfl, he n⟩

/-! ## The pair -/

theorem graph_ext {A : Type} {K L : Graph A} (h : ∀ y x, K.edge y x ↔ L.edge y x) : K = L := by
  cases K; cases L; congr; funext y x; exact propext (h y x)

theorem conj_edge (y x : Ev) : conj.graph.edge y x ↔ pairGraph.edge y x := by
  constructor
  · rintro ⟨g, -, rfl, hm | hm⟩
    · cases g
      · exact Or.inr (Or.inr ⟨hm, rfl⟩)
      · rcases hm with h | h
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr (Or.inl ⟨h, rfl⟩)
    · exact hm.elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨true, trivial, rfl, Or.inl (Or.inl rfl)⟩
    · exact ⟨true, trivial, rfl, Or.inl (Or.inr rfl)⟩
    · exact ⟨false, trivial, rfl, Or.inl rfl⟩

theorem disj_edge (y x : Ev) : disj.graph.edge y x ↔ pairGraph.edge y x := by
  constructor
  · rintro ⟨g, -, rfl, hm | hm⟩
    · cases g
      · exact Or.inl ⟨hm, rfl⟩
      · exact Or.inr (Or.inl ⟨hm, rfl⟩)
      · exact Or.inr (Or.inr ⟨hm, rfl⟩)
    · exact hm.elim
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨.fromS, trivial, rfl, Or.inl rfl⟩
    · exact ⟨.fromU, trivial, rfl, Or.inl rfl⟩
    · exact ⟨.fromT, trivial, rfl, Or.inl rfl⟩

theorem enabling_edge (y x : Ev) : enabling.graph.edge y x ↔ pairGraph.edge y x := by
  constructor
  · rintro ⟨g, -, rfl, hm | ⟨hg, hu⟩⟩
    · cases g
      · exact Or.inr (Or.inr ⟨hm, rfl⟩)
      · exact Or.inl ⟨hm, rfl⟩
    · subst hg
      exact Or.inr (Or.inl ⟨hu, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨true, trivial, rfl, Or.inl rfl⟩
    · exact ⟨true, trivial, rfl, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨false, trivial, rfl, Or.inl rfl⟩

theorem conj_graph : conj.graph = pairGraph := graph_ext conj_edge
theorem disj_graph : disj.graph = pairGraph := graph_ext disj_edge
theorem enabling_graph : enabling.graph = pairGraph := graph_ext enabling_edge

theorem st : pairGraph.edge .s .t := Or.inl ⟨rfl, rfl⟩
theorem ut : pairGraph.edge .u .t := Or.inr (Or.inl ⟨rfl, rfl⟩)
theorem tu : pairGraph.edge .t .u := Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem s_source : pairGraph.Source .s := by
  rintro ⟨y, h | h | h⟩ <;> simp_all

theorem comp_tu : comp pairGraph .t = comp pairGraph .u :=
  (comp_eq_iff _ _ _).2 ⟨.single tu, .single ut⟩

theorem comp_st : comp pairGraph .s ≠ comp pairGraph .t := by
  intro h
  have back := ((comp_eq_iff _ _ _).1 h).2
  cases ReflTransGen.cases_tail back with
  | inl h => cases h
  | inr h =>
    obtain ⟨c, _, hc⟩ := h
    exact s_source ⟨c, hc⟩

theorem pair_least : least pairGraph .s := by
  intro x
  cases x
  · exact .refl
  · exact .single st
  · exact (ReflTransGen.single st).tail tu

theorem pair_comp_cases (C : Comp pairGraph) :
    C = comp pairGraph .s ∨ C = comp pairGraph .t := by
  obtain ⟨e, rfl⟩ := comp_surj _ C
  cases e
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr comp_tu.symm

theorem pair_wcc (e : Ev) : wcc pairGraph e = wcc pairGraph .s := by
  rw [wcc_eq_iff]
  exact .symm _ _ (eqv_of_rtg _ (pair_least e))

instance : Finite Ev := Finite.of_injective (fun e => match e with | Ev.s => (0 : Fin 3) | .t => 1 | .u => 2) (by
  intro a b h; cases a <;> cases b <;> first | rfl | (exact absurd h (by decide)))

theorem finite_wf_ev : WellFounded (condensed pairGraph).edge := finite_wf _

theorem pair_summary : PairSummary := by
  refine ⟨conj_graph, disj_graph, enabling_graph, comp_tu, comp_st, pair_wcc, ?_, pair_least,
    (least_preserved _ _).1 pair_least, pair_comp_cases, ⟨comp_st, _, _, rfl, rfl, st⟩,
    finite_wf_ev⟩
  intro e
  constructor
  · intro h
    cases e
    · rfl
    · exact (h ⟨_, st⟩).elim
    · exact (h ⟨_, tu⟩).elim
  · rintro rfl
    exact s_source

theorem noCycles_of_rank {P : Type} [Preorder P] (K : Graph E) (φ : E → P)
    (h : ∀ y x, K.edge y x → φ y < φ x) : K.NoCycles := by
  have key : ∀ {y x}, TransGen K.edge y x → φ y < φ x := by
    intro y x p
    induction p with
    | single e => exact h _ _ e
    | tail _ e ih => exact ih.trans (h _ _ e)
  exact fun x hx => lt_irrefl _ (key hx)

theorem onOff_coherent {G : Type} (h : Groups Ev G) (allowed : Bool → Prop) (ha : allowed true)
    (hadm : ∀ g, h.admitted g) : (onOff h allowed).coherent :=
  ⟨ha, fun g _ => ⟨hadm g, fun _ _ => Or.inr rfl, Or.inr rfl⟩⟩

theorem onOff_edge {G : Type} (h : Groups Ev G) (allowed : Bool → Prop) (y x : Ev)
    (hex : ∀ g, h.admitted g) :
    (onOff h allowed).exercisedGroups.graph.edge y x ↔ h.graph.edge y x :=
  ⟨fun ⟨g, a, e, m⟩ => ⟨g, a.1, e, m⟩, fun ⟨g, _, e, m⟩ => ⟨g, ⟨hex g, trivial⟩, e, m⟩⟩

theorem onScenario_sufficient {G : Type} (h : Groups Ev G) (g : G) :
    (onOff h onScenario).jointlySufficient g :=
  fun _ hb _ => Or.inr hb

theorem conj_local : LocalPower conj isS allOn := by
  intro e
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  cases e
  · exact Or.inl rfl
  · exact Or.inr ⟨true, trivial, rfl, fun _ _ => trivial⟩
  · exact Or.inr ⟨false, trivial, rfl, fun _ _ => trivial⟩

theorem disj_local : LocalPower disj isS allOn := by
  intro e
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  cases e
  · exact Or.inl rfl
  · exact Or.inr ⟨.fromS, trivial, rfl, fun _ _ => trivial⟩
  · exact Or.inr ⟨.fromT, trivial, rfl, fun _ _ => trivial⟩

theorem enabling_local : LocalPower enabling isS allOn := by
  intro e
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  cases e
  · exact Or.inl rfl
  · exact Or.inr ⟨true, trivial, rfl, fun _ _ => trivial⟩
  · exact Or.inr ⟨false, trivial, rfl, fun _ _ => trivial⟩

theorem powered_allOn {G : Type} (h : Groups Ev G) : PoweredGroups h allOn :=
  fun _ _ _ _ _ => trivial

theorem conj_trap : Trap conj isS cycleEvents := by
  constructor
  · rintro e (rfl | rfl) hi <;> cases hi
  · intro g _ _
    cases g
    · exact ⟨.t, rfl, Or.inl rfl⟩
    · exact ⟨.u, Or.inr rfl, Or.inr rfl⟩

theorem conj_no_t : ¬ Supply conj isS .t := trap_obstruction _ _ _ conj_trap _ (Or.inl rfl)
theorem conj_no_u : ¬ Supply conj isS .u := trap_obstruction _ _ _ conj_trap _ (Or.inr rfl)

theorem disj_supply (e : Ev) : Supply disj isS e := by
  have hs : Supply disj isS .s := .intrinsic _ rfl
  have ht : Supply disj isS .t := Supply.joint (h := disj) .fromS trivial (by
    intro a ha
    cases (ha : a = .s)
    exact hs)
  cases e
  · exact hs
  · exact ht
  · exact Supply.joint (h := disj) .fromT trivial (by
      intro a ha
      cases (ha : a = .t)
      exact ht)

theorem comp_tu_of {K : Graph Ev} (h : K = pairGraph) : comp K .t = comp K .u := by
  subst h; exact comp_tu

theorem conj_condensed_supply (e : Ev) :
    Supply (condenseGroups conj) (condensedIntrinsic conj.graph isS) (comp conj.graph e) := by
  have hs : Supply (condenseGroups conj) (condensedIntrinsic conj.graph isS)
      (comp conj.graph .s) := .intrinsic _ ⟨.s, rfl, rfl⟩
  have ht : Supply (condenseGroups conj) (condensedIntrinsic conj.graph isS)
      (comp conj.graph .t) := by
    refine Supply.joint (h := condenseGroups conj) true trivial ?_
    rintro _ ⟨⟨a, ha, rfl⟩, hne⟩
    rcases (ha : a = .s ∨ a = .u) with rfl | rfl
    · exact hs
    · exact (hne (comp_tu_of conj_graph).symm).elim
  cases e
  · exact hs
  · exact ht
  · rw [← comp_tu_of conj_graph]; exact ht

theorem finite_conj : WellFounded (condensed conj.graph).edge := finite_wf _

theorem conj_no_component : ¬ ComponentEscape conj isS allOn := fun ce =>
  conj_no_t ((supply_iff_component _ _ _ conj_local (powered_allOn _) (finite_wf _)).2 ce .t trivial)

theorem disj_component : ComponentEscape disj isS allOn :=
  (supply_iff_component _ _ _ disj_local (powered_allOn _) (finite_wf _)).1 fun e _ => disj_supply e

theorem supply_split : SupplySplit := by
  refine ⟨?_, onOff_coherent _ _ rfl (fun _ => trivial), onScenario_sufficient _,
    onOff_coherent _ _ rfl (fun _ => trivial), onScenario_sufficient _,
    conj_local, powered_allOn _, disj_local, powered_allOn _,
    .intrinsic _ rfl, conj_no_t, conj_no_u, disj_supply, conj_condensed_supply,
    fun e => supply_forward _ _ _ (disj_supply e), conj_no_component, disj_component, ?_⟩
  · refine graph_ext ?_
    intro y x
    change (onOff conj onScenario).exercisedGroups.graph.edge y.val x.val ↔
      (onOff disj onScenario).exercisedGroups.graph.edge y.val x.val
    rw [onOff_edge _ _ _ _ (fun _ => trivial), onOff_edge _ _ _ _ (fun _ => trivial),
      conj_edge, disj_edge]
  · rintro ⟨F, hF⟩
    have a := hF _ conj isS .t
    have b := hF _ disj isS .t
    rw [conj_graph] at a
    rw [disj_graph] at b
    exact conj_no_t (a.1 (b.2 (disj_supply .t)))

theorem conj_every_sufficient (g : Bool) : (onOff conj everyScenario).jointlySufficient g := by
  intro b _ hm
  cases g
  · rcases hm .t (Or.inl rfl) with h | h
    · cases h
    · exact Or.inr h
  · rcases hm .u (Or.inl (Or.inr rfl)) with h | h
    · cases h
    · exact Or.inr h

theorem cut_comparison : CutComparison := by
  refine ⟨conj_trap, ?_, ?_, onOff_coherent _ _ trivial (fun _ => trivial), conj_every_sufficient,
    ⟨Or.inr rfl, ?_⟩, ⟨Or.inr rfl, fun _ hb _ => Or.inr hb⟩, ?_, ?_,
    ⟨fun _ _ h => h, fun _ _ _ _ => rfl⟩, ?_⟩
  · intro ht
    obtain ⟨a, ha, hd⟩ := ht.2 .fromS trivial (Or.inl rfl)
    cases (ha : a = .s)
    rcases hd with h | h <;> cases h
  · intro hc
    rcases hc.2 .s .t (Or.inl rfl) st with h | h <;> cases h
  · intro hs
    rcases hs false trivial (by
      rintro e (⟨h | h, hne⟩ | h)
      · exact Or.inl h
      · exact (hne h).elim
      · exact h.elim) with h | h <;> cases h
  · exact Supply.joint (h := pruned) true trivial (by
      intro a ha
      cases (ha : a = .s)
      exact .intrinsic _ rfl)
  · exact Supply.joint (h := pruned) false trivial (by
      intro a ha
      cases (ha : a = .t)
      exact Supply.joint (h := pruned) true trivial (by
        intro b hb
        cases (hb : b = .s)
        exact .intrinsic _ rfl))
  · intro ht
    obtain ⟨_, ha, _⟩ := ht.2 () trivial rfl
    exact ha

def evRank : Ev → Nat
  | .s => 0 | .t => 1 | .u => 2

theorem enabler_control : TruthCore.Explanation.CondensationSufficiency.EnablerControl := by
  have hs : Supply enabling isS .s := .intrinsic _ rfl
  have ht : Supply enabling isS .t := Supply.joint (h := enabling) true trivial (by
    intro a ha
    cases (ha : a = .s)
    exact hs)
  have hu : Supply enabling isS .u := Supply.joint (h := enabling) false trivial (by
    intro a ha
    cases (ha : a = .t)
    exact ht)
  have hall : ∀ e, Supply enabling isS e := by
    intro e; cases e
    · exact hs
    · exact ht
    · exact hu
  refine ⟨onOff_coherent _ _ trivial (fun _ => trivial), ?_, enabling_local, powered_allOn _, ?_, ?_,
    hall, (supply_iff_component _ _ _ enabling_local (powered_allOn _) (finite_wf _)).1
      fun e _ => hall e, ?_, ?_⟩
  · intro g b _ hm
    cases g
    · rcases hm .t (Or.inl rfl) with h | h
      · cases h
      · exact Or.inr h
    · rcases hm .u (Or.inr ⟨rfl, rfl⟩) with h | h
      · cases h
      · exact Or.inr h
  · rw [enabling_graph]
    exact fun h => h .t (.tail (.single tu) ut)
  · refine noCycles_of_rank _ evRank ?_
    rintro y x ⟨g, -, rfl, hm | hm⟩
    · cases g
      · cases (hm : y = .t); decide
      · cases (hm : y = .s); decide
    · exact hm.elim
  · intro h
    exact h .t (.tail (.single ⟨false, trivial, rfl, Or.inl rfl⟩)
      ⟨true, trivial, rfl, Or.inl (Or.inr rfl)⟩)
  · intro h
    exact h .t (.tail (.single ⟨DisjGroup.fromT, trivial, rfl, Or.inl rfl⟩)
      ⟨DisjGroup.fromU, trivial, rfl, Or.inl rfl⟩)

/-! ## Infinite controls -/

theorem disjOverlap_edge (y x : Node) : disjOverlap.graph.edge y x ↔ K.edge y x := by
  constructor
  · rintro ⟨⟨n, b⟩, -, rfl, hm | hm⟩
    · cases b
      · cases (hm : y = node (some (n + 1)))
        exact (rfl : n + 1 = n + 1)
      · cases (hm : y = node none)
        exact trivial
    · exact hm.elim
  · rcases y with ⟨_ | m, _⟩ <;> rcases x with ⟨_ | n, _⟩ <;> intro he
    · exact he.elim
    · exact ⟨(n, true), trivial, rfl, Or.inl rfl⟩
    · exact he.elim
    · cases (he : m = n + 1)
      exact ⟨(n, false), trivial, rfl, Or.inl rfl⟩

theorem disjOverlap_supply (e : Node) : Supply disjOverlap intrinsic e := by
  rcases e with ⟨_ | n, _⟩
  · exact .intrinsic _ rfl
  · refine Supply.joint (h := disjOverlap) (n, true) trivial ?_
    intro a ha
    cases (ha : a = node none)
    exact .intrinsic _ rfl

theorem overlap_noCycles : K.NoCycles := by
  obtain ⟨_, hc, _⟩ := rooted_control
  exact hc.2.2.2.1 ()

theorem rooted_branches : RootedBranches := by
  obtain ⟨hg, hc, _, _, hn, _, _, _, _, _, _, _, _, hnoesc⟩ := rooted_control
  have hK : ¬ WellFounded (condensed K).edge := by
    refine not_wf_of_chain K (fun n => node (some n)) (fun n => (rfl : n + 1 = n + 1)) ?_
    intro n h
    have := comp_inj_of_noCycles K overlap_noCycles _ _ h
    have := congrArg Subtype.val this
    simp [node] at this
  have hlocal : LocalPower disjOverlap intrinsic (rooted.occurs rooted.actual) := by
    intro e
    refine ⟨fun _ => ?_, fun _ => Or.inr rfl⟩
    rcases e with ⟨_ | n, _⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨(n, true), trivial, rfl, fun _ _ => Or.inr rfl⟩
  refine ⟨hg, graph_ext disjOverlap_edge, overlap_noCycles, ?_, hK, local_rooted _, fun _ _ _ _ _ => Or.inr rfl,
    acyclic_component _ _ _ (local_rooted _) (by rw [hg]; exact overlap_noCycles), hnoesc, hn,
    disjOverlap_supply,
    (escape_iff _ _ _ hlocal (fun _ _ _ _ _ => Or.inr rfl)).1 fun e _ => disjOverlap_supply e⟩
  rintro ⟨_ | n, _⟩
  · exact .refl
  · exact .single trivial

theorem source_free_chain : SourceFreeChain := by
  obtain ⟨_, _, hl, hn, hs⟩ := source_free_control
  have hc : unrootedGroups.graph.NoCycles := by
    refine noCycles_of_rank (P := ℕᵒᵈ) _ OrderDual.toDual ?_
    rintro y x ⟨g, -, rfl, hm | hm⟩
    · refine OrderDual.toDual_lt_toDual.2 ?_
      rcases hm with rfl | hm
      · exact Nat.lt_succ_self _
      · cases (hm : y = g + 2)
        change g < g + 2
        omega
    · exact hm.elim
  have hp : PoweredGroups unrootedGroups (unrooted.occurs true) := fun _ _ _ _ _ => rfl
  refine ⟨hc, hs, ?_, acyclic_component _ _ _ (hl true) hc, ?_, hn⟩
  · refine not_wf_of_chain _ (fun n => n) ?_ ?_
    · intro n
      exact ⟨n, trivial, rfl, Or.inl (Or.inl rfl)⟩
    · intro n h
      have := comp_inj_of_noCycles _ hc _ _ h
      simp at this
  · intro ee
    exact hn 0 ((escape_iff _ _ _ (hl true) hp).2 ee 0 rfl)

theorem loop_path {a b : Option Nat} (p : ReflTransGen loopChain.graph.edge a b) :
    ∀ m, a = some m → ∃ n, b = some n ∧ n ≤ m := by
  induction p with
  | refl => exact fun m h => ⟨m, h, le_rfl⟩
  | tail _ e ih =>
    intro m hm
    obtain ⟨n, rfl, hle⟩ := ih m hm
    obtain ⟨⟨k, c⟩, -, rfl, hg | hg⟩ := e
    · cases c
      · cases (hg : some n = some (k + 1))
        exact ⟨k, rfl, by omega⟩
      · rcases (hg : some n = none ∨ some n = some k) with h | h
        · cases h
        · cases h
          exact ⟨_, rfl, hle⟩
    · exact hg.elim

theorem loop_inj (a b : Option Nat) (h : comp loopChain.graph a = comp loopChain.graph b) :
    a = b := by
  obtain ⟨p, q⟩ := (comp_eq_iff _ _ _).1 h
  rcases a with _ | m <;> rcases b with _ | n
  · rfl
  · obtain ⟨_, h, _⟩ := loop_path q n rfl
    cases h
  · obtain ⟨_, h, _⟩ := loop_path p m rfl
    cases h
  · obtain ⟨_, h1, h2⟩ := loop_path p m rfl
    obtain ⟨_, h3, h4⟩ := loop_path q n rfl
    cases h1; cases h3
    rw [le_antisymm h2 h4]

theorem loop_control : LoopChainControl := by
  have htrap : Trap loopChain isNone {e | ∃ n, e = some n} := by
    constructor
    · rintro e ⟨n, rfl⟩ hi
      cases hi
    · rintro ⟨k, c⟩ _ _
      cases c
      · exact ⟨some (k + 1), rfl, k + 1, rfl⟩
      · exact ⟨some k, Or.inr rfl, k, rfl⟩
  refine ⟨?_, fun _ _ _ _ _ => trivial, ?_, ?_, ?_, ?_⟩
  · intro e
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    rcases e with _ | n
    · exact Or.inl rfl
    · exact Or.inr ⟨(n, false), trivial, rfl, fun _ _ => trivial⟩
  · refine component_of_singletons _ _ _ loop_inj ?_
    intro e _
    rcases e with _ | n
    · exact Or.inl rfl
    · refine Or.inr ⟨(n, false), trivial, rfl, ?_⟩
      intro h
      have h' : some n = some (n + 1) := h
      simp at h'
  · intro e
    rcases e with _ | n
    · exact .intrinsic _ ⟨none, rfl, rfl⟩
    · refine Supply.joint (h := condenseGroups loopChain) (n, true) trivial ?_
      rintro _ ⟨⟨a, ha, rfl⟩, hne⟩
      rcases (ha : a = none ∨ a = some n) with rfl | rfl
      · exact .intrinsic _ ⟨none, rfl, rfl⟩
      · exact (hne rfl).elim
  · exact fun n => trap_obstruction _ _ _ htrap _ ⟨n, rfl⟩
  · refine not_wf_of_chain _ some (fun n => ⟨(n, false), trivial, rfl, Or.inl rfl⟩) ?_
    intro n h
    have := loop_inj _ _ h
    simp at this

/-! ## Cycle and plural controls -/

theorem circle_edge (y : Bool) : circle.graph.edge y (!y) :=
  ⟨!y, trivial, rfl, Or.inl (show y ≠ !y by cases y <;> decide)⟩

theorem circle_comp (e : Bool) : comp circle.graph e = comp circle.graph false := by
  cases e
  · rfl
  · exact (comp_eq_iff _ _ _).2 ⟨.single (circle_edge true), .single (circle_edge false)⟩

theorem cycle_control : CycleControl := by
  obtain ⟨_, ⟨_, hl, hn⟩, _⟩ := TruthCore.Results.Causality.DerivativeJointPower.controls
  have hsup : ∀ e, Supply circle (fun e => e = false) e := by
    have h0 : Supply circle (fun e => e = false) false := .intrinsic _ rfl
    intro e
    cases e
    · exact h0
    · refine Supply.joint (h := circle) true trivial ?_
      intro a ha
      have : a = false := by
        cases a
        · rfl
        · exact (ha rfl).elim
      subst this
      exact h0
  have hl2 : LocalPower circle (fun e => e = false) (fun _ => True) := by
    intro e
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    cases e
    · exact Or.inl rfl
    · exact Or.inr ⟨true, trivial, rfl, fun _ _ => trivial⟩
  have hp : PoweredGroups circle (fun _ => True) := fun _ _ _ _ _ => trivial
  refine ⟨circle_comp true |>.symm, ?_, ?_, finite_wf _, ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial, trivial⟩⟩,
    hl, ?_, hn, ?_, hsup,
    (supply_iff_component _ _ _ hl2 hp (finite_wf _)).1 (fun e _ => hsup e), disj_supply, ?_⟩
  · exact fun e h => h ⟨!e, by simpa using circle_edge (!e)⟩
  · rintro ⟨A, hne, y, x, rfl, hx, _⟩
    exact hne (circle_comp y)
  · intro f _
    exact ⟨!f, f, trivial, trivial, rfl, show (!f) ≠ f by cases f <;> decide⟩
  · intro ce
    exact hn false ((supply_iff_component _ _ _ hl hp (finite_wf _)).2 ce false trivial)
  · intro h
    obtain ⟨_, g, _, _, he, _⟩ := h .s (Or.inl rfl)
    cases g <;> cases he

open TruthCore.Explanation.UltimateAdequacy in
open TruthCore.Results.Explanation.UltimateAdequacy in
theorem plural_control : PluralControl := by
  have hzero : ∀ g, (groups .plural).graph.edge 0 (g + 2) :=
    fun g => ⟨g, trivial, rfl, Or.inl (Or.inl rfl)⟩
  have hone : ∀ g, (groups .plural).graph.edge 1 (g + 2) :=
    fun g => ⟨g, trivial, rfl, Or.inl (Or.inr rfl)⟩
  refine ⟨plural_supply, ?_, ?_, source_preserved _ _ plural_sources.1,
    source_preserved _ _ plural_sources.2, ?_⟩
  · intro e
    rw [wcc_eq_iff]
    match e with
    | 0 => exact .refl _
    | 1 => exact .trans _ _ _ (.rel _ _ (hone 0)) (.symm _ _ (.rel _ _ (hzero 0)))
    | g + 2 => exact .symm _ _ (.rel _ _ (hzero g))
  · intro h
    have p := ((comp_eq_iff _ _ _).1 h).1
    cases ReflTransGen.cases_tail p with
    | inl h => exact absurd h (by decide)
    | inr h =>
      obtain ⟨c, _, hc⟩ := h
      exact plural_sources.2 ⟨c, hc⟩
  · rintro ⟨C, hC⟩
    obtain ⟨s, rfl⟩ := comp_surj _ C
    exact plural_no_least ⟨s, (least_preserved _ _).2 hC⟩

section PluralSupport
open TruthCore.Explanation.UltimateAdequacy
open TruthCore.Results.Explanation.UltimateAdequacy

/-- The #735 plural model has exactly the TWO intrinsic contributors 0 and 1
as its minimal support for target 2. One complete group record does not
collapse their joint productive requirement to a single individual. -/
theorem plural_minimal_intrinsic_support :
    MinimalIntrinsicSupport (groups .plural) (intrinsic .plural)
      ({0, 1} : Set Nat) 2 := by
  have hSupply : Supply (groups .plural)
      (fun x => x ∈ ({0, 1} : Set Nat)) 2 := by
    apply Supply.joint 0 trivial
    intro a ha
    change a = 0 ∨ a = 1 at ha
    exact .intrinsic a ha
  refine ⟨⟨?_, hSupply⟩, ?_⟩
  · intro x hx
    change x = 0 ∨ x = 1 at hx
    exact hx
  · intro T hT _
    have hNoTarget : (2 : Nat) ∉ T := by
      intro h2
      have hi := hT.1 h2
      change (2 : Nat) = 0 ∨ (2 : Nat) = 1 at hi
      omega
    have h0 : (0 : Nat) ∈ T :=
      required_unproduced_seed (groups .plural) T 2 0 hNoTarget
        (by intro g _ _; change (0 : Nat) = 0 ∨ (0 : Nat) = 1; exact Or.inl rfl)
        (by intro g _ he; change g + 2 = 0 at he; omega)
        hT.2
    have h1 : (1 : Nat) ∈ T :=
      required_unproduced_seed (groups .plural) T 2 1 hNoTarget
        (by intro g _ _; change (1 : Nat) = 0 ∨ (1 : Nat) = 1; exact Or.inr rfl)
        (by intro g _ he; change g + 2 = 1 at he; omega)
        hT.2
    intro x hx
    change x = 0 ∨ x = 1 at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact h1

/-- The plural target has no OTHER intrinsic support set: both distinct
intrinsic roots are required by its one admitted complete group. -/
theorem plural_intrinsic_support_unique (T : Set Nat)
    (hT : IntrinsicSupport (groups .plural) (intrinsic .plural) T 2) :
    T = ({0, 1} : Set Nat) := by
  have hSub : T ⊆ ({0, 1} : Set Nat) := by
    intro x hx
    have hi := hT.1 hx
    change x = 0 ∨ x = 1 at hi
    exact hi
  exact Set.Subset.antisymm hSub
    (plural_minimal_intrinsic_support.2 T hT hSub)

/-- The same #735 jointly productive two-root configuration is a boundary for
the new complete-production subgraph route: NO edge-subgraph on all its event
nodes can simultaneously be connected and satisfy both complete-producer
cover policies, regardless of the ambient parthood PartialOrder. It can still
retain its complete GROUP record and its two productive partial contributors.
This does not identify events with substances or group records with bearers. -/
theorem plural_no_spanning_complete_subgraph [PartialOrder Nat]
    (K : Graph Nat) (participants : Nat → Set Nat)
    (hIncluded : ∀ a b, K.edge a b → (groups .plural).graph.edge a b)
    (hProducer : TruthCore.Causality.CompleteCauseContributorCover.ProducerParticipates
      K participants)
    (hCover : TruthCore.Causality.CompleteCauseContributorCover.CompleteCauseCoversContributors
      K participants) :
    ¬ TruthCore.Causality.SourceForest.WeaklyConnected K := by
  intro hConnected
  have hUnique :=
    TruthCore.Results.Causality.CompleteCauseSourceUniqueness.atMostOne_subgraph
      K (groups .plural).graph participants hIncluded hProducer hCover hConnected
  exact (by decide : (0 : Nat) ≠ 1)
    (hUnique 0 1 plural_sources.1 plural_sources.2)

end PluralSupport

/-- On #752's fixed graph, the conjunctive cyclic record has no sufficient
set of its allowed intrinsic event s, even though the graph has source s. -/
theorem conj_no_intrinsic_support (S : Set Ev) :
    ¬ IntrinsicSupport conj isS S .t := by
  intro hS
  apply conj_no_t
  exact support_mono conj hS.1 hS.2

/-- Alternative one-contributor records have the singleton {s} as a minimal
intrinsic support of t. The same ordinary edge graph gave no support in conj. -/
theorem disj_minimal_intrinsic_support :
    MinimalIntrinsicSupport disj isS ({Ev.s} : Set Ev) .t := by
  apply singleton_minimal disj isS .s .t rfl
  · intro g _
    cases g with
    | fromS => exact ⟨.s, rfl⟩
    | fromU => exact ⟨.u, rfl⟩
    | fromT => exact ⟨.t, rfl⟩
  · exact disj_supply .t

theorem disj_intrinsic_support_unique (T : Set Ev)
    (hT : IntrinsicSupport disj isS T .t) :
    T = ({Ev.s} : Set Ev) :=
  singleton_support_unique disj isS .s .t (fun _ h => h)
    disj_minimal_intrinsic_support T hT

/-- A required enabler is NOT part of the productive support set. Switching
u from contributor to enabler keeps the graph but restores {s} as the
minimal productive supply basis of t. -/
theorem enabling_minimal_intrinsic_support :
    MinimalIntrinsicSupport enabling isS ({Ev.s} : Set Ev) .t := by
  apply singleton_minimal enabling isS .s .t rfl
  · intro g _
    cases g
    · exact ⟨.t, rfl⟩
    · exact ⟨.s, rfl⟩
  · apply Supply.joint true trivial
    intro a ha
    change a = Ev.s at ha
    subst a
    exact .intrinsic _ rfl

theorem enabling_intrinsic_support_unique (T : Set Ev)
    (hT : IntrinsicSupport enabling isS T .t) :
    T = ({Ev.s} : Set Ev) :=
  singleton_support_unique enabling isS .s .t (fun _ h => h)
    enabling_minimal_intrinsic_support T hT

/-- Condensation preserves reachability, weak connection and leastness and
receives Supply. On a three-event carrier, no function of the projected graph and intrinsic set decides
Supply. Over a well-founded condensation, under LocalPower and PoweredGroups,
Supply of every active event coincides with escape inside components; fixed
models test each hypothesis. Supply is not defended here as actual explanation. -/
theorem certificate : TruthCore.Explanation.CondensationSufficiency.Certificate :=
  ⟨graph_invariants, supply_schema, pair_summary, supply_split, cut_comparison, enabler_control,
    rooted_branches, source_free_chain, loop_control, cycle_control, plural_control⟩

end TruthCore.Results.Explanation.CondensationSufficiency
