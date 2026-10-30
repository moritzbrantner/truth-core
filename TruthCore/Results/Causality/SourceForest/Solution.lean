import TruthCore.Causality.SourceForest
import TruthCore.Results.Causality.WorldSourceRegress.Solution
namespace TruthCore.Results.Causality.SourceForest
open TruthCore.Logic.Regress
open TruthCore.Causality.SourceForest

/-- Left uniqueness is a sufficient local diamond condition for Mathlib's
Church–Rosser theorem on reversed causal edges. -/
theorem confluent_of_uniquePredecessor {Node : Type} (G : Graph Node)
    (hPred : UniquePredecessor G) : UpstreamConfluent G := by
  intro a b c hab hac
  exact Relation.church_rosser (fun _ x y hx hy => by
    have hxy : x = y := hPred hx hy
    subst y
    exact ⟨x, .refl, .refl⟩) hab hac

/-- Confluence joins upstream paths. Mathlib's equivalence of Join makes weak
connectivity sufficient for two sources to have a common ancestor; each
source forces that ancestor to be itself. No WF is used. -/
theorem atMostOne_of_confluent {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hConfluent : UpstreamConfluent G) :
    AtMostOneSource G := by
  let upstream := fun a b => G.edge b a
  have hJoin : Equivalence (Relation.Join (Relation.ReflTransGen upstream)) :=
    Relation.equivalence_join hConfluent
  have hConnectedJoin : ∀ a b, Relation.EqvGen G.edge a b →
      Relation.Join (Relation.ReflTransGen upstream) a b := by
    intro a b hab
    induction hab with
    | rel a b he => exact ⟨a, .refl, .single he⟩
    | refl a => exact hJoin.refl a
    | symm a b _ ih => exact hJoin.symm ih
    | trans a b c _ _ ih₁ ih₂ => exact hJoin.trans ih₁ ih₂
  intro a b ha hb
  obtain ⟨s, has, hbs⟩ := hConnectedJoin a b (hConnected a b)
  have hsa : s = a := Relation.reflTransGen_iff_eq (fun y he => ha ⟨y, he⟩) |>.mp has
  have hsb : s = b := Relation.reflTransGen_iff_eq (fun y he => hb ⟨y, he⟩) |>.mp hbs
  exact hsa.symm.trans hsb

theorem atMostOne {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hPred : UniquePredecessor G) :
    AtMostOneSource G :=
  atMostOne_of_confluent G hConnected (confluent_of_uniquePredecessor G hPred)

/-- Compose the existing accessibility-to-source-path theorem: first obtain a
source, then identify every pointwise source-path endpoint with it. For
G := actualGraph m w, population means actual existence in the fixed world. -/
theorem rooted_of_confluent {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hConfluent : UpstreamConfluent G)
    (hWF : WellFoundedEdges G) (hPop : Populated G) :
    RootedAtUniqueSource G := by
  obtain ⟨x⟩ := hPop
  obtain ⟨s, _, hs⟩ := WorldSourceRegress.sourcePath_of_acc G x (hWF.apply x)
  have hOne := atMostOne_of_confluent G hConnected hConfluent
  refine ⟨s, hs, fun t ht => hOne t s ht hs, ?_⟩
  intro y
  obtain ⟨t, hp, ht⟩ := WorldSourceRegress.sourcePath_of_acc G y (hWF.apply y)
  exact (hOne t s ht hs) ▸ hp

theorem rooted {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hPred : UniquePredecessor G)
    (hWF : WellFoundedEdges G) (hPop : Populated G) :
    RootedAtUniqueSource G :=
  rooted_of_confluent G hConnected (confluent_of_uniquePredecessor G hPred) hWF hPop

theorem controls : OmissionControls := by
  have hForkWF : WellFoundedEdges fork := by
    let rank : ForkNode → Nat := fun n => match n with | .a => 0 | .b => 0 | .c => 1
    apply Subrelation.wf (r := fun x y => rank x < rank y) ?_
      (InvImage.wf rank Nat.lt_wfRel.wf)
    intro x y he
    cases x <;> cases y <;> simp_all [fork, rank]
  have hForkConnected : WeaklyConnected fork := by
    have toC : ∀ x, Relation.EqvGen fork.edge x .c := by
      intro x
      cases x
      · exact .rel _ _ ⟨Or.inl rfl, rfl⟩
      · exact .rel _ _ ⟨Or.inr rfl, rfl⟩
      · exact .refl _
    intro x y
    exact .trans _ _ _ (toC x) (.symm _ _ (toC y))
  have hIsolatedPred : UniquePredecessor isolated := by
    intro x y z h
    exact h.elim
  have hIsolatedWF : WellFoundedEdges isolated := ⟨fun x => .intro x (fun _ h => h.elim)⟩
  have hChainConnected : WeaklyConnected chain := by
    have from0 : ∀ z : Int, Relation.EqvGen chain.edge 0 z := by
      intro z
      induction z using Int.induction_on with
      | zero => exact .refl _
      | succ i ih => exact .trans _ _ _ ih (.symm _ _ (.rel _ _ rfl))
      | pred i ih =>
        apply Relation.EqvGen.trans _ _ _ ih
        exact .rel _ _ (by change -(i : Int) = -(i : Int) - 1 + 1; omega)
    intro a b
    exact .trans _ _ _ (.symm _ _ (from0 a)) (from0 b)
  have hChainPred : UniquePredecessor chain := by
    intro a b c ha hb
    exact ha.trans hb.symm
  have hChainNoSource : ¬ ∃ s, chain.Source s := by
    rintro ⟨s, hs⟩
    exact hs ⟨s + 1, rfl⟩
  have hChainNotWF : ¬ WellFoundedEdges chain := by
    intro hw
    obtain ⟨s, _, hs⟩ := WorldSourceRegress.sourcePath_of_acc chain 0 (hw.apply 0)
    exact hChainNoSource ⟨s, hs⟩
  refine ⟨⟨hForkConnected, hForkWF, (Graph.controls_of_wellFounded fork hForkWF).1,
    ?_, ?_, ?_, ForkNode.noConfusion⟩,
    ⟨hIsolatedPred, hIsolatedWF, ?_, ?_, ?_⟩,
    ⟨hChainConnected, hChainPred, atMostOne chain hChainConnected hChainPred,
      hChainNotWF, hChainNoSource⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro hp
    have : ForkNode.a = .b := hp ⟨Or.inl rfl, rfl⟩ ⟨Or.inr rfl, rfl⟩
    exact ForkNode.noConfusion this
  · rintro ⟨_, _, h⟩; exact ForkNode.noConfusion h
  · rintro ⟨_, _, h⟩; exact ForkNode.noConfusion h
  · intro hc
    have h : ∀ a b, Relation.EqvGen isolated.edge a b → a = b := by
      intro a b he
      induction he with
      | rel a b h => exact h.elim
      | refl => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact Bool.noConfusion (h false true (hc false true))
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨_, h⟩; exact h
  · intro x; exact x.elim
  · intro x; exact x.elim
  · exact ⟨fun x => x.elim⟩
  · intro x; exact x.elim
  · rintro ⟨x⟩; exact x.elim
  · rintro ⟨x, _⟩; exact x.elim

theorem confluence_strictness : ConfluenceStrictnessControl := by
  have toRoot : ∀ x, Relation.ReflTransGen (fun a b => diamond.edge b a) x .root := by
    intro x
    cases x
    · exact .refl
    · exact .single (Or.inl ⟨rfl, Or.inl rfl⟩)
    · exact .single (Or.inl ⟨rfl, Or.inr rfl⟩)
    · exact show Relation.ReflTransGen (fun a b => diamond.edge b a) DiamondNode.tip .root from
        (Relation.ReflTransGen.single (b := DiamondNode.left)
          (Or.inr ⟨Or.inl rfl, rfl⟩)).trans
          (.single (Or.inl ⟨rfl, Or.inl rfl⟩))
  have hc : UpstreamConfluent diamond := fun _ x y _ _ => ⟨.root, toRoot x, toRoot y⟩
  have hn : WeaklyConnected diamond := by
    have toRootEqv : ∀ x, Relation.EqvGen diamond.edge x .root := by
      have flipEqv : ∀ x y, Relation.EqvGen (fun a b => diamond.edge b a) x y →
          Relation.EqvGen diamond.edge x y := by
        intro x y he
        induction he with
        | rel a b h => exact .symm _ _ (.rel _ _ h)
        | refl => exact .refl _
        | symm a b _ ih => exact .symm _ _ ih
        | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
      intro x
      exact flipEqv _ _ (Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (toRoot x))
    intro x y
    exact .trans _ _ _ (toRootEqv x) (.symm _ _ (toRootEqv y))
  have hw : WellFoundedEdges diamond := by
    let rank : DiamondNode → Nat := fun x => match x with
      | .root => 0 | .left => 1 | .right => 1 | .tip => 2
    apply Subrelation.wf (r := fun x y => rank x < rank y) ?_
      (InvImage.wf rank Nat.lt_wfRel.wf)
    intro x y he
    cases x <;> cases y <;> simp_all [diamond, rank]
  refine ⟨hc, hn, hw, ?_, rooted_of_confluent diamond hn hc hw ⟨.root⟩⟩
  intro hp
  have : DiamondNode.left = .right :=
    hp (Or.inr ⟨Or.inl rfl, rfl⟩) (Or.inr ⟨Or.inr rfl, rfl⟩)
  exact DiamondNode.noConfusion this
end TruthCore.Results.Causality.SourceForest
