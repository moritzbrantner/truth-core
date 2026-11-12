module
public import TruthCore.Causality.ConcreteRootAccess
public import TruthCore.Results.Causality.ClosedGroundingRoots.Solution

/-! General fixed-profile deductions, including empty and nonactual inventories.
Excluded middle is an explicit input where used; no choice or new axiom. -/
@[expose] public section
namespace TruthCore.Results.Causality.ConcreteRootAccess
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.ClosedGroundingRoots
open TruthCore.Causality.ConcreteRootAccess
open TruthCore.Logic (ExcludedMiddle)

theorem closedOfAccess {W B : Type} (m : Profile W B) (w : W)
    (h : UniversalRootAccess m w) : ClosedGroundingCollectionsRooted m w := by
  intro S hS hn x hx
  have stay : ∀ z, RootAccess m w z → S z → False := by
    intro z hz
    induction hz with
    | root hr => exact fun hs => hn _ hs hr
    | step hp hc hg ih => exact fun hs => ih (hS.2 _ _ hs hg)
  exact stay x (h x (hS.1 x hx)) hx

theorem accessOfClosed {W B : Type} (m : Profile W B) (w : W)
    (h : ClosedGroundingCollectionsRooted m w) (em : ExcludedMiddle) :
    UniversalRootAccess m w := by
  intro x hc
  rcases em (RootAccess m w x) with ha | hn
  · exact ha
  · exfalso
    apply h (fun z => ActualConcrete m w z ∧ ¬ RootAccess m w z) ?_ ?_ x ⟨hc, hn⟩
    · refine ⟨fun z hz => hz.1, ?_⟩
      intro z y hz hg
      exact ⟨⟨hg.1, hg.2.1⟩, fun hy => hz.2 (.step hy hz.1 hg)⟩
    · intro z hz hr
      exact hz.2 (.root hr)

theorem borrowedOfClosed {W B : Type} (m : Profile W B) (w : W)
    (h : ClosedGroundingCollectionsRooted m w) : NoWhollyBorrowedCollection m w := by
  intro S hS hb
  apply h S ⟨hS.1, fun x y hx hg => hS.2 x y hx hg.2.1 hg.2.2⟩
  intro x hx hr
  apply hb x hx
  intro y hy
  have hs := hS.2 x y hx hy.1 hy.2
  exact hr.2 y ⟨(hS.1 y hs).1, hy⟩

theorem localizedOfClosed {W B : Type} (m : Profile W B) (w : W)
    (h : ClosedGroundingCollectionsRooted m w) (em : ExcludedMiddle) :
    LocalizedBridge m w := by
  intro x y hx _ _ _
  exact accessOfClosed m w h em x hx

theorem closedOfLocalized {W B : Type} (m : Profile W B) (w : W)
    (hb : NoWhollyBorrowedCollection m w) (hl : LocalizedBridge m w)
    (em : ExcludedMiddle) : ClosedGroundingCollectionsRooted m w := by
  intro S hS hn
  have noAccess : ∀ z, RootAccess m w z → S z → False := by
    intro z hz
    induction hz with
    | root hr => exact fun hs => hn _ hs hr
    | step hp hc hg ih => exact fun hs => ih (hS.2 _ _ hs hg)
  refine hb S ⟨hS.1, ?_⟩ ?_
  · intro x y hx he hg
    rcases em (m.concrete y) with hc | hc
    · exact hS.2 x y hx ⟨hc, he, hg⟩
    · exact (noAccess x (hl x y (hS.1 x hx) he hc hg) hx).elim
  · intro x hx hall
    exact hn x hx ⟨hS.1 x hx, fun y hy => hall y ⟨hy.2.1, hy.2.2⟩⟩

theorem rootAccessEquivalence {W B : Type} (m : Profile W B) (w : W)
    (em : ExcludedMiddle) : RootAccessEquivalence m w :=
  ⟨fun h => accessOfClosed m w h em, closedOfAccess m w⟩

theorem borrowedDecomposition {W B : Type} (m : Profile W B) (w : W)
    (em : ExcludedMiddle) : BorrowedDecomposition m w :=
  ⟨fun h => ⟨borrowedOfClosed m w h, localizedOfClosed m w h em⟩,
    fun h => closedOfLocalized m w h.1 h.2 em⟩

theorem blanketEquivalence {W B : Type} (m : Profile W B) (w : W)
    (hc : ActualSuppliersOfConcretaConcrete m w) : BlanketEquivalence m w :=
  ⟨borrowedOfClosed m w, fun hb =>
    TruthCore.Results.Causality.ClosedGroundingRoots.closedRootedOfBorrowed m w hb hc⟩
end TruthCore.Results.Causality.ConcreteRootAccess
