import TruthCore.Causality.DerivativeJointPower
import TruthCore.Results.Causality.JointGroups.Solution
import TruthCore.Results.Causality.TemporalActualization.Controls.Solution
import TruthCore.Results.Causality.EssentialPowerUnderdetermined.Solution
import TruthCore.Results.Causality.FiniteGroundingLimitNotClosed.Solution
import TruthCore.Results.Causality.LocalObservationSelectsSolution.Solution
namespace TruthCore.Results.Causality.DerivativeJointPower
open TruthCore.Causality TruthCore.Logic.Regress
open TruthCore.Causality.JointGroups TruthCore.Causality.WorldSourceRegress
open TruthCore.Causality.DerivativeJointPower
variable {E G : Type}

theorem trap_obstruction (h : Groups E G) (I : E → Prop) (D : Set E)
    (ht : Trap h I D) : ∀ e ∈ D, ¬ Supply h I e := by
  intro e he hs
  induction hs with
  | intrinsic e hi => exact ht.1 e he hi
  | joint g hg _ ih =>
    obtain ⟨a, ha, hd⟩ := ht.2 g hg he
    exact ih a ha hd

/-- Exact equivalence within LocalPower, not an independent defense of Escape.
It exposes how much selecting the inductive standard commits one to. -/
theorem escape_iff (h : Groups E G) (I A : E → Prop) (_hl : LocalPower h I A) (hc : PoweredGroups h A) :
    (∀ e, A e → Supply h I e) ↔ Escape h I A := by
  classical
  constructor
  · intro hs D hD hn
    by_contra hnEscape
    have ht : Trap h I D := by
      constructor
      · intro e he hi
        exact hnEscape (Or.inl ⟨e, he, hi⟩)
      · intro g hg hd
        by_contra hm
        apply hnEscape
        right
        refine ⟨g, hg, hd, ?_⟩
        intro e he hde
        exact hm ⟨e, he, hde⟩
    obtain ⟨e, he⟩ := hn
    exact trap_obstruction h I D ht e he (hs e (hD he))
  · intro escape e ha
    by_contra hns
    let D : Set E := {x | A x ∧ ¬ Supply h I x}
    rcases escape D (fun _ hx => hx.1) ⟨e, ha, hns⟩ with ⟨x, hx, hi⟩ | ⟨g, hg, hd, hm⟩
    · exact hx.2 (.intrinsic x hi)
    · apply hd.2
      apply Supply.joint g hg
      intro x hx
      by_contra hnx
      exact hm x hx ⟨hc g hg hd.1 x hx, hnx⟩

theorem source_path (h : Groups E G) (I : E → Prop)
    (hne : ∀ g, h.admitted g → (h.contributors g).Nonempty)
    (e : E) (hs : Supply h I e) :
    ∃ s, FiniteCausalPath h.graph.edge e s ∧ I s := by
  induction hs with
  | intrinsic e hi => exact ⟨e, .same e, hi⟩
  | joint g hg _ ih =>
    obtain ⟨a, ha⟩ := hne g hg
    obtain ⟨s, hp, hi⟩ := ih a ha
    exact ⟨s, .link ⟨g, hg, rfl, Or.inl ha⟩ hp, hi⟩

theorem graph_grounded (x : Node) : FinitelyGroundedPower H.graph.edge intrinsic x := by
  cases x with
  | mk x hx =>
    cases x with
    | none => exact .intrinsic _ rfl
    | some n =>
      apply FinitelyGroundedPower.borrowed (y := node none)
      · rw [JointGroups.recorded_graph]
        exact trivial
      · exact .intrinsic _ rfl

theorem branch_trap : Trap H intrinsic branch := by
  constructor
  · rintro e ⟨n, hn⟩ hi
    simp [intrinsic, hn] at hi
  · intro g _ hd
    obtain ⟨n, hn⟩ := hd
    change g.val.val = some n at hn
    refine ⟨node (some (n + 1)), ?_, n + 1, rfl⟩
    change TruthCore.Results.Causality.GroundingAllowsRegress.link _ g.val.val
    rw [hn]
    rfl

theorem source_member (g : {x : Node // ∃ y, K.edge y x}) : node none ∈ H.members g := by
  obtain ⟨y, hy⟩ := g.property
  change TruthCore.Results.Causality.GroundingAllowsRegress.link y.val g.val.val at hy
  cases hg : g.val.val with
  | none => simp [hg, TruthCore.Results.Causality.GroundingAllowsRegress.link] at hy
  | some n => exact Or.inl (by change TruthCore.Results.Causality.GroundingAllowsRegress.link none g.val.val; rw [hg]; trivial)

theorem local_rooted (s : Bool) : LocalPower H intrinsic (rooted.occurs s) := by
  intro e
  constructor
  · intro he
    rcases he with hi | hon
    · exact Or.inl hi
    · cases hx : e.val with
      | none => exact Or.inl hx
      | some n =>
        right
        refine ⟨group n, trivial, Subtype.ext hx.symm, ?_⟩
        intro a _
        exact Or.inr hon
  · rintro (hi | ⟨g, _, he, hm⟩)
    · exact Or.inl hi
    · cases hx : e.val with
      | none => exact Or.inl hx
      | some n =>
        have mem : node (some (n + 1)) ∈ H.contributors g := by
          change TruthCore.Results.Causality.GroundingAllowsRegress.link _ g.val.val
          have eq : g.val.val = some n := congrArg Subtype.val he |>.trans hx
          rw [eq]
          rfl
        rcases hm _ mem with hi | hon
        · simp [intrinsic, node] at hi
        · exact Or.inr hon

theorem rooted_coherent : rooted.coherent := by
  refine ⟨trivial, ?_⟩
  intro g _
  exact ⟨trivial, fun _ _ => Or.inr rfl, Or.inr rfl⟩

theorem rooted_suffices (g) : rooted.jointlySufficient g := by
  intro s _ hm
  exact (local_rooted s (H.effect g)).mpr (Or.inr ⟨g, trivial, rfl, fun e he => hm e (Or.inl he)⟩)

theorem branch_indispensable (n : Nat) :
    rooted.indispensable (group n) (node (some (n + 1))) := by
  constructor
  · exact rfl
  · intro hs
    have failure := hs false trivial (by
      intro e he
      rcases he with ⟨hm, hne⟩ | hempty
      · change TruthCore.Results.Causality.GroundingAllowsRegress.link e.val (some n) at hm
        cases hx : e.val with
        | none => exact Or.inl hx
        | some k =>
          have hk : k = n + 1 := by simpa [hx, TruthCore.Results.Causality.GroundingAllowsRegress.link] using hm
          have heq : e = node (some (n + 1)) := Subtype.ext (hx.trans (congrArg some hk))
          exact (hne heq).elim
      · exact hempty.elim)
    rcases failure with hi | hon
    · simp [intrinsic, rooted, H, recorded, group, node] at hi
    · exact Bool.noConfusion hon

theorem rooted_control : RootedControl := by
  refine ⟨JointGroups.recorded_graph K, JointGroups.overlap.2.2.2, ?_,
    .intrinsic _ rfl, ?_, source_member, rooted_coherent, rooted_suffices,
    local_rooted, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    rw [← Graph.grounded_eq_lfp]
    exact graph_grounded e
  · intro n
    exact trap_obstruction H intrinsic branch branch_trap _ ⟨n, rfl⟩
  · exact branch_indispensable
  · exact ⟨rfl, rooted_coherent.2⟩
  · intro g s _ hm
    exact rooted_suffices g s trivial hm
  · intro s
    rfl
  · intro he
    have hs := (escape_iff H intrinsic (rooted.occurs true) (local_rooted true) (fun _ _ _ _ _ => Or.inr rfl)).mpr he
    exact trap_obstruction H intrinsic branch branch_trap _ ⟨0, rfl⟩
      (hs (node (some 0)) (Or.inr rfl))

theorem finite_supply : Supply finite (fun e => e = false) true := by
  apply Supply.joint () trivial
  intro e he
  have heq : e = false := by simpa [finite, Groups.members] using he
  exact .intrinsic e heq

theorem controls : Controls := by
  have hf : LocalPower finite (fun e => e = false) (fun _ => True) := by
    intro e
    cases e
    · exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
    · exact ⟨fun _ => Or.inr ⟨(), trivial, rfl, fun _ _ => trivial⟩, fun _ => trivial⟩
  refine ⟨⟨finite_supply, hf, ?_⟩, ⟨TemporalActualization.Controls.controls, ?_, ?_⟩,
    .intrinsic false trivial, ?_, ?_⟩
  · apply (escape_iff finite _ _ hf (fun _ _ _ _ _ => trivial)).mp
    intro e _
    cases e
    · exact .intrinsic false rfl
    · exact finite_supply
  · intro e
    refine ⟨fun _ => Or.inr ⟨e, trivial, rfl, fun _ _ => trivial⟩, fun _ => trivial⟩
  · intro e
    apply trap_obstruction circle (fun _ => False) Set.univ _ e trivial
    refine ⟨fun _ _ => id, ?_⟩
    intro g _ _
    exact ⟨!g, (by change (!g) ≠ g; cases g <;> decide), trivial⟩
  · apply Supply.joint false trivial
    intro e he
    exact he.elim
  · apply Supply.joint () trivial
    intro e he
    exact he.elim

theorem enabler_control : EnablerControl := by
  refine ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial, trivial⟩⟩, ?_, rfl, ?_⟩
  · apply Supply.joint () trivial
    intro e he
    exact .intrinsic e he
  · intro hs
    cases hs with
    | intrinsic _ hi => exact (by decide : (2 : Fin 3) ≠ 0) hi

theorem admission_omission : AdmissionOmission := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [LocalPower, alternatives]
  · intro D hD hn
    obtain ⟨e, he⟩ := hn
    have heq : e = true := hD he
    subst e
    right
    refine ⟨true, trivial, he, ?_⟩
    intro x hx hxd
    have hxfalse : x = false := hx
    have hxtrue : x = true := hD hxd
    exact Bool.noConfusion (hxfalse.symm.trans hxtrue)
  · apply trap_obstruction alternatives (fun _ => False) Set.univ _ true trivial
    refine ⟨fun _ _ => id, ?_⟩
    intro g _ _
    exact ⟨if g then false else true, rfl, trivial⟩
  · intro hp
    have bad := hp true trivial rfl false rfl
    exact Bool.noConfusion bad
  · apply Supply.joint true trivial
    intro e he
    exact .intrinsic e he

theorem source_free_control : SourceFreeControl := by
  have local_rule (s : Bool) : LocalPower unrootedGroups (fun _ => False) (unrooted.occurs s) := by
    intro e
    refine ⟨fun hs => Or.inr ⟨e, trivial, rfl, fun _ _ => hs⟩, ?_⟩
    rintro (bad | ⟨g, _, _, hm⟩)
    · exact bad.elim
    · exact hm (g + 1) (Or.inl rfl)
  refine ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => rfl, rfl⟩⟩, ?_, local_rule, ?_, ?_⟩
  · intro g s _ hm
    exact hm (g + 1) (Or.inl (Or.inl rfl))
  · intro e
    apply trap_obstruction unrootedGroups (fun _ => False) Set.univ _ e trivial
    exact ⟨fun _ _ => id, fun g _ _ => ⟨g + 1, Or.inl rfl, trivial⟩⟩
  · intro e hs
    exact hs ⟨e + 1, e, trivial, rfl, Or.inl (Or.inl rfl)⟩

theorem context_controls : ContextControls :=
  ⟨fun _ _ => ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩,
   fun _ _ => ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩,
   fun _ _ => ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl⟩⟩⟩

/-- New all-member obstruction and cut equivalence with explicit rival models;
no actual inductive-selection or metaphysical possibility claim. -/
theorem certificate : TruthCore.Causality.DerivativeJointPower.Certificate :=
  ⟨⟨fun _ _ => trap_obstruction, fun _ _ => escape_iff, fun _ _ => source_path⟩,
    rooted_control, controls, enabler_control, admission_omission,
    ⟨EssentialPowerUnderdetermined.essentialPowerUnderdetermined,
    LocalObservationSelectsSolution.localObservationSelectsSolution,
    FiniteGroundingLimitNotClosed.finiteGroundingLimitNotClosed⟩,
    source_free_control, context_controls⟩
end TruthCore.Results.Causality.DerivativeJointPower
