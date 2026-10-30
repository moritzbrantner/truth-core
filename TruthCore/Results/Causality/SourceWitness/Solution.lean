import TruthCore.Causality.SourceWitness
import TruthCore.Results.Causality.SourceForest.Solution
namespace TruthCore.Results.Causality.SourceWitness
open TruthCore.Logic.Regress
open TruthCore.Causality
open TruthCore.Causality.SourceForest
open TruthCore.Causality.SourceWitness
open TruthCore.Causality.WorldSourceRegress

/-- Joinability with a source collapses the source's upstream path to length
zero. Convert Mathlib's reversed finite closure to the existing causal path. -/
theorem path_to_source {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hConfluent : UpstreamConfluent G)
    (s : Node) (hs : G.Source s) (x : Node) : FiniteCausalPath G.edge x s := by
  let upstream := fun a b => G.edge b a
  have hJoin : Equivalence (Relation.Join (Relation.ReflTransGen upstream)) :=
    Relation.equivalence_join hConfluent
  let : IsEquiv Node (Relation.Join (Relation.ReflTransGen upstream)) := hJoin.isEquiv
  have hxs : Relation.Join (Relation.ReflTransGen upstream) x s :=
    Relation.EqvGen.eqvGen_le (fun a _ he => ⟨a, .refl, .single he⟩) x s (hConnected x s)
  obtain ⟨t, hxt, hst⟩ := hxs
  have hts : t = s :=
    Relation.reflTransGen_iff_eq (fun y he => hs ⟨y, he⟩) |>.mp hst
  subst t
  induction hxt using Relation.ReflTransGen.head_induction_on with
  | refl => exact .same s
  | head he _ ih => exact .link he ih

theorem rooted_from_source {Node : Type} (G : Graph Node)
    (hConnected : WeaklyConnected G) (hConfluent : UpstreamConfluent G)
    (hSource : HasSource G) : RootedAtUniqueSource G := by
  obtain ⟨s, hs⟩ := hSource
  exact ⟨s, hs, fun t ht => SourceForest.atMostOne_of_confluent G hConnected hConfluent t s ht hs,
    path_to_source G hConnected hConfluent s hs⟩

/-- Reuse the earlier overlapControl for acyclicity, the selected infinite
chain and non-Acc; do not change or replace its literal link interpretation. -/
theorem overlap_control : ConfluentOverlapControl := by
  let G := actualGraph overlap ()
  let noneNode : Actual overlap () := ⟨none, True.intro⟩
  have toNone : ∀ x, Relation.ReflTransGen (fun a b => G.edge b a) x noneNode := by
    rintro ⟨x, hx⟩
    cases x
    · exact .refl
    · exact .single True.intro
  have hc : UpstreamConfluent G := fun _ x y _ _ => ⟨noneNode, toNone x, toNone y⟩
  have hn : WeaklyConnected G := by
    have toNoneEqv : ∀ x, Relation.EqvGen G.edge x noneNode := by
      rintro ⟨x, hx⟩
      cases x
      · exact .refl _
      · exact .symm _ _ (.rel _ _ True.intro)
    intro x y
    exact .trans _ _ _ (toNoneEqv x) (.symm _ _ (toNoneEqv y))
  have old := WorldSourceRegress.overlapControl
  obtain ⟨s, _, hs⟩ := old.2.1
  have hr := rooted_from_source G hn hc ⟨s, hs⟩
  exact ⟨hn, hc, hr, old.1, old.2.2.1, old.2.2.2.1,
    fun hw => old.2.2.2.1 (hw.apply overlapNode)⟩
end TruthCore.Results.Causality.SourceWitness
