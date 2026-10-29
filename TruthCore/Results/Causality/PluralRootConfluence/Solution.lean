import TruthCore.Causality.PluralRootConfluence
import TruthCore.Results.Causality.PartFreePlurality.Solution
import TruthCore.Results.Causality.SourceWitness.Solution

namespace TruthCore.Results.Causality.PluralRootConfluence
open TruthCore.Causality.PartFreePlurality
open TruthCore.Causality.PluralRootConfluence
open TruthCore.Causality.SourceForest
open TruthCore.Logic.Regress

/-- Apply the unchanged #684 joint certificate and #634 rooted theorem to one
literal actual graph. The contradiction is the missing confluence input, not
failure of source existence, connectivity, or well-foundedness. -/
theorem control : Control := by
  have hl : graph.Source (node .left) := by
    rintro ⟨y, hy⟩
    exact Nat.not_lt_zero (rank y.val) hy
  have hr : graph.Source (node .right) := by
    rintro ⟨y, hy⟩
    exact Nat.not_lt_zero (rank y.val) hy
  have hne : node .left ≠ node .right := by
    intro he
    have := congrArg Subtype.val he
    exact Being.noConfusion this
  have hConnected : WeaklyConnected graph := by
    have toEffect : ∀ x, Relation.EqvGen graph.edge x (node .effect) := by
      rintro ⟨x, hx⟩
      cases x with
      | left => exact .rel _ _ (by change 0 < 3; decide)
      | right => exact .rel _ _ (by change 0 < 3; decide)
      | constituent => exact .rel _ _ (by change 1 < 3; decide)
      | instrument => exact .rel _ _ (by change 2 < 3; decide)
      | effect => exact .refl _
    intro x y
    exact .trans _ _ _ (toEffect x) (.symm _ _ (toEffect y))
  have hWF : WellFoundedEdges graph :=
    Subrelation.wf (fun h => h) (InvImage.wf (fun x : TruthCore.Causality.WorldSourceRegress.Actual ontic false => rank x.val) Nat.lt_wfRel.wf)
  have hNotRooted : ¬ RootedAtUniqueSource graph := by
    rintro ⟨s, hs, hone, _⟩
    exact hne ((hone _ hl).trans (hone _ hr).symm)
  have hNotConfluent : ¬ UpstreamConfluent graph := by
    intro hc
    exact hNotRooted (SourceWitness.rooted_from_source graph hConnected hc ⟨node .left, hl⟩)
  have hNoJoin : ¬ Relation.Join (Relation.ReflTransGen (fun x y => graph.edge y x))
      (node .left) (node .right) := by
    rintro ⟨s, hls, hrs⟩
    have hsl : s = node .left :=
      Relation.reflTransGen_iff_eq (fun y he => hl ⟨y, he⟩) |>.mp hls
    have hsr : s = node .right :=
      Relation.reflTransGen_iff_eq (fun y he => hr ⟨y, he⟩) |>.mp hrs
    exact hne (hsl.symm.trans hsr)
  exact ⟨PartFreePlurality.jointControl, rfl, hConnected, hWF, hl, hr, hne,
    (by change 0 < 2; decide), (by change 0 < 2; decide), hNoJoin,
    hNotConfluent, hNotRooted⟩
end TruthCore.Results.Causality.PluralRootConfluence
