import TruthCore.Explanation.UltimateAdequacy
import TruthCore.Results.Causality.DerivativeJointPower.Solution
import TruthCore.Results.Explanation.HistorySelection.Solution
import TruthCore.Results.Explanation.TargetCopyExpansion.Solution
import TruthCore.Results.Epistemology.UltimateExplanation.Solution
import TruthCore.Results.Explanation.ConservativeReasonExpansion.Solution
namespace TruthCore.Results.Explanation.UltimateAdequacy
open TruthCore.Explanation.UltimateAdequacy
open TruthCore.Causality.JointGroups TruthCore.Causality.DerivativeJointPower
open TruthCore.Logic.Regress
open TruthCore.German.Kant.CosmologicalInference

 theorem actual_occurs (k : Kind) (e : Nat) : (exercise k).occurs (exercise k).actual e := by
  cases k with
  | single => rfl
  | chain => rfl
  | branch => exact Or.inr rfl
  | plural =>
    dsimp [exercise]
    split_ifs <;> first | rfl | exact ⟨rfl,rfl⟩

 theorem local_actual (k : Kind) : LocalPower (groups k) (intrinsic k) ((exercise k).occurs (exercise k).actual) := by
  intro e
  refine ⟨fun _ => ?_, fun _ => actual_occurs k e⟩
  cases k with
  | single =>
    cases e with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, trivial, rfl, fun _ _ => rfl⟩
  | plural =>
    cases e with
    | zero => exact Or.inl (Or.inl rfl)
    | succ n =>
      cases n with
      | zero => exact Or.inl (Or.inr rfl)
      | succ n => exact Or.inr ⟨n, trivial, rfl, fun a _ => actual_occurs .plural a⟩
  | branch =>
    cases e with
    | zero => exact Or.inl rfl
    | succ n => exact Or.inr ⟨n, trivial, rfl, fun a _ => actual_occurs .branch a⟩
  | chain => exact Or.inr ⟨e, trivial, rfl, fun _ _ => rfl⟩

 theorem background (k : Kind) : Background k := by
  refine ⟨⟨trivial, fun g _ => ⟨trivial, fun e _ => actual_occurs k e, actual_occurs k _⟩⟩,
    ?_, actual_occurs k, local_actual k, fun _ _ _ e _ => actual_occurs k e,
    fun _ _ => ⟨rfl, rfl, fun _ _ => ⟨rfl,rfl⟩⟩, ?_⟩
  · intro g s _ hm
    cases k with
    | single => exact hm 0 (Or.inl rfl)
    | plural =>
      have ha := hm 0 (Or.inl (Or.inl rfl))
      have hb := hm 1 (Or.inl (Or.inr rfl))
      change s.1 = true at ha
      change s.2 = true at hb
      change (if g+2 = 0 then s.1 = true else if g+2 = 1 then s.2 = true else s.1 = true ∧ s.2 = true)
      rw [ite_eq_right (by omega : g+2 ≠ 0), ite_eq_right (by omega : g+2 ≠ 1)]
      exact ⟨ha,hb⟩
    | branch =>
      have ha := hm (g+2) (Or.inl (Or.inr rfl))
      rcases ha with bad | hon
      · omega
      · exact Or.inr hon
    | chain => exact hm (g+1) (Or.inl (Or.inl rfl))
  · intro y x
    constructor
    · rintro ⟨g,_,he,hm⟩
      exact ⟨g,trivial,he,hm⟩
    · rintro ⟨g,_,he,hm⟩
      exact ⟨g,⟨trivial,trivial⟩,he,hm⟩

 theorem single_supply (e : Nat) : Supply (groups .single) (intrinsic .single) e := by
  cases e with
  | zero => exact .intrinsic _ rfl
  | succ n =>
    apply Supply.joint n trivial
    intro a ha
    exact .intrinsic a ha

 theorem plural_supply (e : Nat) : Supply (groups .plural) (intrinsic .plural) e := by
  cases e with
  | zero => exact .intrinsic _ (Or.inl rfl)
  | succ n =>
    cases n with
    | zero => exact .intrinsic _ (Or.inr rfl)
    | succ n =>
      apply Supply.joint n trivial
      intro a ha
      exact .intrinsic a ha

 theorem plural_sources : (groups .plural).graph.Source 0 ∧ (groups .plural).graph.Source 1 := by
  constructor <;> rintro ⟨y,g,_,he,_⟩ <;> change g+2 = _ at he <;> omega

 theorem end_source {E : Type} (K : Graph E) (s x : E) (hs : K.Source x)
    (hp : Relation.ReflTransGen K.edge s x) : s = x := by
  cases hp with
  | refl => rfl
  | tail _ he => exact (hs ⟨_,he⟩).elim

 theorem plural_no_least : ¬ ∃ s, least (groups .plural).graph s := by
  rintro ⟨s,hs⟩
  have h0 := end_source _ s 0 plural_sources.1 (hs 0)
  have h1 := end_source _ s 1 plural_sources.2 (hs 1)
  omega

 theorem single_least : least (groups .single).graph 0 := by
  intro e
  cases e with
  | zero => exact .refl
  | succ n => exact .single ⟨n,trivial,rfl,Or.inl rfl⟩

 theorem branch_least : least (groups .branch).graph 0 := by
  intro e
  cases e with
  | zero => exact .refl
  | succ n => exact .single ⟨n,trivial,rfl,Or.inl (Or.inl rfl)⟩

 theorem branch_trap : Trap (groups .branch) (intrinsic .branch) {n | n ≠ 0} := by
  refine ⟨fun _ hn hi => hn hi, ?_⟩
  intro g _ _
  exact ⟨g+2, Or.inr rfl, by change g+2 ≠ 0; omega⟩

 theorem branch_no_supply : ¬ Supply (groups .branch) (intrinsic .branch) 2 :=
  TruthCore.Results.Causality.DerivativeJointPower.trap_obstruction _ _ _ branch_trap 2 (by decide)

 theorem plural_indispensable : (exercise .plural).indispensable 0 0 ∧ (exercise .plural).indispensable 0 1 := by
  constructor
  · refine ⟨Or.inl rfl, ?_⟩
    intro hs
    have bad := hs (false,true) trivial (by
      intro e he
      rcases he with ⟨he,hn⟩ | hf
      · rcases he with he | he
        · exact (hn he).elim
        · subst e; rfl
      · exact hf.elim)
    exact Bool.noConfusion bad.1
  · refine ⟨Or.inr rfl, ?_⟩
    intro hs
    have bad := hs (true,false) trivial (by
      intro e he
      rcases he with ⟨he,hn⟩ | hf
      · rcases he with he | he
        · subst e; rfl
        · exact (hn he).elim
      · exact hf.elim)
    exact Bool.noConfusion bad.2

 theorem branch_indispensable : (exercise .branch).indispensable 1 3 := by
  refine ⟨Or.inr rfl, ?_⟩
  intro hs
  have bad := hs (false,true) trivial (by
    intro e he
    rcases he with ⟨he,hn⟩ | hf
    · rcases he with he | he
      · exact Or.inl he
      · exact (hn he).elim
    · exact hf.elim)
  rcases bad with bad | bad
  · change (2 : Nat) = 0 at bad; omega
  · exact Bool.noConfusion bad

 theorem chain_no_supply (e : Nat) : ¬ Supply (groups .chain) (intrinsic .chain) e := by
  apply TruthCore.Results.Causality.DerivativeJointPower.trap_obstruction _ _ Set.univ _ e trivial
  exact ⟨fun _ _ => id, fun g _ _ => ⟨g+1,Or.inl rfl,trivial⟩⟩

/-- Literal source-freedom of the named chain interpretation. -/
theorem chain_no_source (e : Nat) : ¬ (groups .chain).graph.Source e := by
  intro hs
  exact hs ⟨e+1,e,trivial,rfl,Or.inl (Or.inl rfl)⟩

 theorem chain_no_least : ¬ ∃ s, least (groups .chain).graph s := by
  rintro ⟨s,hs⟩
  have bound : ∀ x y, Relation.ReflTransGen (groups .chain).graph.edge x y → y ≤ x := by
    intro x y hp
    induction hp with
    | refl => exact Nat.le_refl _
    | @tail z _ _ he ih =>
      obtain ⟨g,_,heq,hm⟩ := he
      change g = _ at heq
      rcases hm with hm | hf
      · rcases hm with hm | hm <;> omega
      · exact hf.elim
  have := bound s (s+1) (hs (s+1))
  omega

 theorem decode_encode (e : TruthCore.Causality.DerivativeJointPower.Node) : decode (encode e) = e := by
  apply Subtype.ext
  rcases e with ⟨e,he⟩
  cases e <;> rfl
 theorem encode_decode (n : Nat) : encode (decode n) = n := by cases n <;> rfl

 theorem branch_edge (y x : TruthCore.Causality.DerivativeJointPower.Node) :
    TruthCore.Causality.DerivativeJointPower.K.edge y x ↔
    (groups .branch).graph.edge (encode y) (encode x) := by
  rcases y with ⟨y,hy⟩
  rcases x with ⟨x,hx⟩
  cases x with
  | none =>
    constructor
    · intro hf
      cases y <;> exact hf.elim
    · rintro ⟨g,_,he,_⟩
      change g+1 = 0 at he
      omega
  | some n =>
    cases y with
    | none =>
      exact ⟨fun _ => ⟨n,trivial,rfl,Or.inl (Or.inl rfl)⟩,fun _ => trivial⟩
    | some m =>
      constructor
      · intro he
        change m = n+1 at he
        subst m
        exact ⟨n,trivial,rfl,Or.inl (Or.inr rfl)⟩
      · rintro ⟨g,_,he,hm⟩
        change g+1 = n+1 at he
        have hgn := Nat.succ.inj he
        subst g
        rcases hm with hm | hf
        · rcases hm with hm | hm
          · change m+1 = 0 at hm; omega
          · change m+1 = (n+1)+1 at hm
            exact Nat.succ.inj hm
        · exact hf.elim

 theorem branch_supply (e : TruthCore.Causality.DerivativeJointPower.Node) :
    Supply TruthCore.Causality.DerivativeJointPower.H
      TruthCore.Causality.DerivativeJointPower.intrinsic e ↔
    Supply (groups .branch) (intrinsic .branch) (encode e) := by
  cases hx : e.val with
  | none =>
    have he : e = TruthCore.Causality.DerivativeJointPower.node none := Subtype.ext hx
    subst e
    exact ⟨fun _ => .intrinsic _ rfl, fun _ => .intrinsic _ rfl⟩
  | some n =>
    have he : e = TruthCore.Causality.DerivativeJointPower.node (some n) := Subtype.ext hx
    subst e
    have old := TruthCore.Results.Causality.DerivativeJointPower.rooted_control.2.2.2.2.1 n
    have hn : encode (TruthCore.Causality.DerivativeJointPower.node (some n)) ≠ 0 := by change n+1 ≠ 0; omega
    have new := TruthCore.Results.Causality.DerivativeJointPower.trap_obstruction _ _ _ branch_trap _ hn
    exact ⟨fun h => (old h).elim, fun h => (new h).elim⟩

 theorem structural : Structural :=
  ⟨background,single_supply,single_least,plural_supply,plural_indispensable.1,
    plural_indispensable.2,plural_sources.1,plural_sources.2,plural_no_least,
    branch_least,branch_no_supply,branch_indispensable,chain_no_supply,chain_no_least,
    decode_encode,encode_decode,branch_edge,branch_supply⟩

/-- This necessity is a property of the stipulated modal extension, not a
consequence from intrinsic productive power to the bearer's necessary being. -/
theorem intrinsic_necessary (k : Kind) (e : Nat)
    (hi : TruthCore.Explanation.UltimateAdequacy.intrinsic k e) :
    NecessaryAt (modal k false) false e :=
  fun _ _ => Or.inr (Or.inr hi)

 theorem not_intrinsic_target (k : Kind) : ¬ TruthCore.Explanation.UltimateAdequacy.intrinsic k 2 := by
  cases k <;> dsimp [TruthCore.Explanation.UltimateAdequacy.intrinsic] <;> decide

 theorem modal_contingent (k : Kind) : ContingentAt (modal k false) false 2 := by
  refine ⟨Or.inl rfl,true,trivial,?_⟩
  intro h
  rcases h with h | h | h
  · exact Bool.noConfusion h
  · exact Bool.noConfusion h
  · exact not_intrinsic_target k h

 theorem modal_controls : ModalControls := by
  refine ⟨fun _ _ _ => Or.inl rfl, ?_, fun _ _ _ _ => Or.inr (Or.inl rfl),
    modal_contingent, ?_, ?_, ?_⟩
  · intro k b y x
    exact ⟨fun h => h.2.2, fun h => ⟨Or.inl rfl,Or.inl rfl,h⟩⟩
  · intro k
    apply TruthCore.Results.Explanation.HistorySelection.no_selection (history k) (fun (_ : Bool) (_ : Unit) => True)
      (fun _ => True) false true trivial
    · intro hs
      have bad := (hs 2 ()).mpr (Or.inl rfl)
      change true = false ∨ false = true ∨ TruthCore.Explanation.UltimateAdequacy.intrinsic k 2 at bad
      rcases bad with hf | hf | hi
      · exact Bool.noConfusion hf
      · exact Bool.noConfusion hf
      · exact not_intrinsic_target k hi
    · exact fun _ _ => Iff.rfl
  · intro k
    refine ⟨fun _ _ => trivial, ?_⟩
    intro hn
    exact TruthCore.Causality.BruteFoundationExplanations.contingentExcludesNecessaryNecessitatingReason
      (reasons k) false () 2 (modal_contingent k) (fun _ _ => trivial) hn
  · intro k b
    exact TruthCore.Results.Explanation.TargetCopyExpansion.copiedCoverage _

/-- Transport the ORIGINAL selected some0 branch to node1. The comparison
explanandum remains node2; no incidental anchored property is moved to it. -/
theorem transported_branch : TruthCore.Causality.WorldSourceRegress.AnchoredRegress
    (groups .branch).graph 1 := by
  have old := TruthCore.Results.Causality.SourceWitness.overlap_control.2.2.2.2.1
  obtain ⟨f,h0,hi,he⟩ := old
  refine ⟨fun n => encode (f n), ?_, ?_, fun n => (branch_edge _ _).mp (he n)⟩
  · change encode (f 0) = 1
    rw [h0]; rfl
  · intro a b hab
    apply hi
    exact (decode_encode (f a)).symm.trans ((congrArg decode hab).trans (decode_encode (f b)))

 theorem certificate : TruthCore.Explanation.UltimateAdequacy.Certificate :=
  ⟨structural,modal_controls⟩
end TruthCore.Results.Explanation.UltimateAdequacy

namespace TruthCore.Results.Explanation.UltimateAdequacy
 theorem epistemic_comparison : TruthCore.Explanation.UltimateAdequacy.EpistemicComparison :=
  ⟨TruthCore.Results.Epistemology.UltimateExplanation.integration,
    fun k b => TruthCore.Results.Explanation.ConservativeReasonExpansion.checks.1 Bool Nat
      (TruthCore.Explanation.UltimateAdequacy.modal k b)⟩
end TruthCore.Results.Explanation.UltimateAdequacy
