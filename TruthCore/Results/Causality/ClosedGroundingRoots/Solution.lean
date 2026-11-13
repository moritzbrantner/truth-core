module

public import TruthCore.Causality.ClosedGroundingRoots
public import TruthCore.Results.Causality.NecessaryConcreteUnderived.Solution
public import TruthCore.Results.Causality.NecessarySupportCoverage.Solution
public import TruthCore.Results.Causality.QuantitativeTransferPaths.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ClosedGroundingRoots

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.NecessarySupportActualScope
open TruthCore.Causality.NecessaryConcreteRouteBridge (NecessaryActualRootAt ActualGroundingAsymmetric)
open TruthCore.Causality.ClosedGroundingRoots
open TruthCore.Causality.ClosedGroundingRoots.Control
open TruthCore.Causality.QuantitativeTransferPaths (Path)
open TruthCore.German.Kant.CosmologicalInference (NecessaryAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Well-founded actual grounding implies the closed-collection condition, with no
excluded middle: by well-founded induction no actual concretum belongs to a
ground-closed collection without a root. -/
theorem closedRootedOfWF {W B : Type} (m : Profile W B) (w : W)
    (hWF : ActualGroundingWF m w) : ClosedGroundingCollectionsRooted m w := by
  intro S hS hNoRoot
  have key : ∀ a : {x // ActualConcrete m w x}, ¬ S a.1 := by
    intro a
    induction a using hWF.induction with
    | _ a ih =>
      intro haS
      exact hNoRoot a.1 haS
        ⟨a.2, fun y hy => ih ⟨y, hy.1, hy.2.1⟩ hy.2.2 (hS.2 a.1 y haS hy)⟩
  intro x hx
  exact key ⟨x, hS.1 x hx⟩ hx

/-- An inhabited world satisfying the closed-collection condition has an actual
root: otherwise all actual concreta form a nonempty ground-closed collection
without a root. -/
theorem actualRootOfClosedRooted {W B : Type} (m : Profile W B) (w : W)
    (hEM : ExcludedMiddle) (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hC : ClosedGroundingCollectionsRooted m w) : ∃ x, ActualRoot m w x := by
  rcases hEM (∃ x, ActualRoot m w x) with h | h
  · exact h
  · obtain ⟨x, hc, he⟩ := hPop
    exact (hC (ActualConcrete m w) ⟨fun _ hy => hy, fun _ y _ hy => ⟨hy.1, hy.2.1⟩⟩
      (fun y _ hr => h ⟨y, hr⟩) x ⟨hc, he⟩).elim

/-- A necessary actual root, from the closed-collection condition, inhabitedness,
grounding of every actual contingent concretum and excluded middle. -/
theorem necessaryActualRootOfClosedRooted {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryActualRootAt m w := by
  obtain ⟨x, hr⟩ := actualRootOfClosedRooted m w hEM hPop hC
  rcases hEM (NecessaryAt m.ontic w x) with hn | hn
  · exact ⟨x, hr, hn⟩
  · exact ((everyContingentGrounded_iff_noContingentRoot m w hEM).mp hDep
      (contingentRootOfNonnecessary m w hEM ⟨x, hr, hn⟩)).elim

/-- A necessary concretum from the closed-collection condition: the AGWF-free
form of `NecessaryRootFork.necessaryConcreteOfActualGrounded`. -/
theorem necessaryConcreteOfClosedRooted {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteAt m w := by
  obtain ⟨x, hr, hn⟩ := necessaryActualRootOfClosedRooted m w hPop hC hDep hEM
  exact ⟨x, hr.1.1, hr.1.2, hn⟩

/-- The join's endpoint from the actual necessary root and coverage, with the
closed-collection condition in place of AGWF. -/
theorem underivedOfCoverageClosed {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hCov : NecessarySupportActuallyCovered m w) :
    NecessaryConcreteUnderivedAt m w := by
  obtain ⟨x, ⟨⟨hc, he⟩, hroot⟩, hn⟩ := necessaryActualRootOfClosedRooted m w hPop hC hDep hEM
  refine ⟨x, hc, he, hn, ?_⟩
  intro v a ha hav hg
  obtain ⟨c, hcc, hce, hcg⟩ := hCov v a x ha hc hn hav hg
  exact hroot c ⟨hcc, hce, hcg⟩

/-- The join's endpoint from a necessary concretum, J1 and coverage, with the
closed-collection condition in place of AGWF: if no necessary concretum were
underived, the actual necessary concreta would form a nonempty collection, closed
under actual grounds by J1, with no root (by coverage a root would be underived). -/
theorem underivedFromNecessityOfCoverageClosed {W B : Type} (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hCov : NecessarySupportActuallyCovered m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  rcases hEM (NecessaryConcreteUnderivedAt m w) with h | hNone
  · exact h
  · exfalso
    obtain ⟨b, hc, he, hn⟩ := hNecessary
    refine hC (fun x => ActualConcrete m w x ∧ NecessaryAt m.ontic w x)
      ⟨fun _ hx => hx.1, ?_⟩ ?_ b ⟨⟨hc, he⟩, hn⟩
    · intro x y hx hy
      exact ⟨⟨hy.1, hy.2.1⟩, hNoCont w ⟨y, hy.1⟩ ⟨x, hx.1.1⟩ hy.2.1 hx.2 hy.2.2⟩
    · intro x hx hr
      apply hNone
      refine ⟨x, hx.1.1, hx.1.2, hx.2, ?_⟩
      intro v a ha hav hg
      obtain ⟨c, hcc, hce, hcg⟩ := hCov v a x ha hx.1.1 hx.2 hav hg
      exact hr.2 c ⟨hcc, hce, hcg⟩

/-- The same with the actual-world instance J1@w of J1. -/
theorem underivedFromNecessityOfActualCoverageClosed {W B : Type} (m : Profile W B) (w : W)
    (hNecessary : NecessaryConcreteAt m w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hAct : ActualNoContingentConcreteSupport m w)
    (hCov : NecessarySupportActuallyCovered m w) (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  rcases hEM (NecessaryConcreteUnderivedAt m w) with h | hNone
  · exact h
  · exfalso
    obtain ⟨b, hc, he, hn⟩ := hNecessary
    refine hC (fun x => ActualConcrete m w x ∧ NecessaryAt m.ontic w x)
      ⟨fun _ hx => hx.1, ?_⟩ ?_ b ⟨⟨hc, he⟩, hn⟩
    · intro x y hx hy
      exact ⟨⟨hy.1, hy.2.1⟩, hAct ⟨y, hy.1⟩ ⟨x, hx.1.1⟩ hy.2.1 hx.2 hy.2.2⟩
    · intro x hx hr
      apply hNone
      refine ⟨x, hx.1.1, hx.1.2, hx.2, ?_⟩
      intro v a ha hav hg
      obtain ⟨c, hcc, hce, hcg⟩ := hCov v a x ha hx.1.1 hx.2 hav hg
      exact hr.2 c ⟨hcc, hce, hcg⟩

/-- The `checks` route of the join with the closed-collection condition in place
of AGWF: the necessary concretum comes from the closed-collection condition, the
rest is the existing modal union route. -/
theorem checksClosed {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hC : ClosedGroundingCollectionsRooted m w)
    (hDep : EveryContingentGroundedAt m w)
    (hRef : ActualReflexive m.ontic w)
    (hNoCont : NoContingentConcreteSupport m w)
    (hUnion : ConcreteNecessaryUnionWF m w)
    (hEM : ExcludedMiddle) :
    NecessaryConcreteUnderivedAt m w := by
  obtain ⟨b, hc, he, hn⟩ := necessaryConcreteOfClosedRooted m w hPop hC hDep hEM
  have hNecessary : TruthCore.German.Kant.CosmologicalInference.NecessaryBeing
      (concreteOntic m) w := ⟨⟨b, hc⟩, he, hn⟩
  obtain ⟨target, ht, hn, hu⟩ :=
    TruthCore.Results.Causality.NecessarilyUnderived.PositiveUnion.checks
      (concreteOntic m) (concreteSupport m) w hNecessary hRef hNoCont hUnion hEM
  refine ⟨target.val, target.property, ht, hn, ?_⟩
  intro v a ha he hEdge
  exact hu v ⟨a, ha⟩ he hEdge

/-- The per se attenuation bridge gives the closed-collection condition. The
network analogues `binaryFixed` and `halfFixed` show that `finitePath` fails
without uniform loss or without the common bound; no Profile-level control. From any
member of a ground-closed collection, the weighted-network theorem `finitePath`
finds a finite path of positive receptions to a thing with positive own esse;
each reception is an actual grounding edge, so the path stays inside the
collection, and its end is an actual root. -/
theorem closedRootedOfAttenuation {W B : Type} (m : Profile W B) (w : W)
    (h : AttenuatedEsseReception m w) : ClosedGroundingCollectionsRooted m w := by
  obtain ⟨hCount, wt, s, P, q, M, hq, hq1, hM, hw, hs, hbound, hsum, hrow, hprod, hbal,
    hEdge, hOwn, hPos⟩ := h
  intro S hS hNoRoot x hx
  have hP : ∀ v, 0 ≤ P v := fun v => le_of_lt (hPos v)
  obtain ⟨u, hpath, hsu⟩ :=
    TruthCore.Results.Causality.QuantitativeTransferPaths.finitePath (V := _)
      wt s P q M hq hq1 hM hw hs hP hbound hsum hrow hprod hbal ⟨x, hS.1 x hx⟩
      (hPos _)
  have stay : ∀ v, Path wt ⟨x, hS.1 x hx⟩ v → S v.1 := by
    intro v hv
    induction hv with
    | refl => exact hx
    | @tail b c _ hbc ih =>
      exact hS.2 b.1 c.1 ih ⟨c.2.1, c.2.2, hEdge b c hbc⟩
  exact hNoRoot u.1 (stay u hpath) ⟨u.2, hOwn u hsu⟩

/-- The borrowed-reality principle over all modelled suppliers gives the
closed-collection condition, given that actual concreta are supplied only by
concreta: a ground-closed rootless collection is then closed under all actual
suppliers, and each member has one. -/
theorem closedRootedOfBorrowed {W B : Type} (m : Profile W B) (w : W)
    (hBR : NoWhollyBorrowedCollection m w)
    (hConc : ActualSuppliersOfConcretaConcrete m w) :
    ClosedGroundingCollectionsRooted m w := by
  intro S hS hNoRoot
  refine hBR S ⟨hS.1, fun x y hx hy hg => hS.2 x y hx ⟨hConc x y (hS.1 x hx) hy hg, hy, hg⟩⟩ ?_
  intro x hx hall
  exact hNoRoot x hx ⟨hS.1 x hx, fun y hy => hall y ⟨hy.2.1, hy.2.2⟩⟩

/-! ## Controls -/

theorem limitGrounder_none_root : ActualRoot limitGrounder () none := by
  refine ⟨⟨trivial, trivial⟩, ?_⟩
  rintro y ⟨-, -, h | ⟨n, -, h⟩⟩
  · exact h.2 rfl
  · exact nomatch h

theorem limitGrounderControl : LimitGrounderControl := by
  refine ⟨?_, ?_, ⟨none, trivial, trivial⟩, ?_, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S hS hNoRoot x hx
    cases x with
    | none => exact hNoRoot none hx limitGrounder_none_root
    | some n =>
      exact hNoRoot none (hS.2 (some n) none hx ⟨trivial, trivial, Or.inl ⟨rfl, nofun⟩⟩)
        limitGrounder_none_root
  · refine TruthCore.Results.Causality.NecessarySupportCoverage.not_wf_of_pred _
      (fun a => ∃ n, a.1 = some n) ?_ ⟨some 0, trivial, trivial⟩ ⟨0, rfl⟩
    rintro ⟨a, ha⟩ ⟨n, rfl⟩
    exact ⟨⟨some (n+1), trivial, trivial⟩, ⟨n+1, rfl⟩, Or.inr ⟨n, rfl, rfl⟩⟩
  · rintro x - - ⟨-, v, -, hv⟩
    exact (hv trivial).elim
  · intro _ _ _ _ _ _ _ _; trivial
  · intro _ _ _ _ _ _ _; trivial
  · rintro ⟨⟩ a b ha _ _ _ hg
    exact ⟨a, ha, trivial, hg⟩
  · rintro ⟨⟩ _ _ _ _ _ hg
    exact hg
  · refine TruthCore.Results.Causality.NecessarySupportCoverage.not_wf_of_pred _
      (fun a => ∃ n, a.1 = some n) ?_ ⟨some 0, trivial⟩ ⟨0, rfl⟩
    rintro ⟨a, ha⟩ ⟨n, rfl⟩
    exact ⟨⟨some (n+1), trivial⟩, ⟨n+1, rfl⟩, fun _ _ => trivial, fun _ _ => trivial, (),
      trivial, Or.inr ⟨n, rfl, rfl⟩⟩
  · refine ⟨none, trivial, trivial, fun _ _ => trivial, ?_⟩
    rintro v a - - (h | ⟨n, -, h⟩)
    · exact h.2 rfl
    · exact nomatch h
  · rintro a b - - (h | ⟨n, rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n+1, n, rfl, rfl, Nat.lt_succ_self n⟩
  · rintro y (h | ⟨n, k, -, h, -⟩)
    · exact h.2 rfl
    · exact nomatch h
  · refine TruthCore.Results.Causality.NecessarySupportCoverage.not_wf_of_pred _
      (fun a => ∃ n, a = some n) ?_ (some 0) ⟨0, rfl⟩
    rintro a ⟨n, rfl⟩
    exact ⟨some (n+1), ⟨n+1, rfl⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
      Or.inr ⟨n+1, n, rfl, rfl, Nat.lt_succ_self n⟩⟩

theorem pureRegressControl : PureRegressControl := by
  refine ⟨?_, ⟨0, trivial, trivial, fun _ _ => trivial⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hC
    refine hC (fun _ => True) ⟨fun _ _ => ⟨trivial, trivial⟩, fun _ _ _ _ => trivial⟩ ?_ 0 trivial
    intro x _ hr
    exact hr.2 (x+1) ⟨trivial, trivial, rfl⟩
  · rintro x - - ⟨-, v, -, hv⟩
    exact (hv trivial).elim
  · intro _ _ _ _ _ _ _ _; trivial
  · intro _ _ _ _ _ _ _; trivial
  · rintro ⟨⟩ a b ha _ _ _ hg
    exact ⟨a, ha, trivial, hg⟩
  · rintro a b - - rfl
    exact Nat.lt_succ_self b
  · rintro ⟨b, -, -, -, hu⟩
    exact hu () (b+1) trivial trivial rfl

theorem rootedCycleControl : RootedCycleControl := by
  have hroot : ActualRoot rootedCycle () none := by
    refine ⟨⟨trivial, trivial⟩, ?_⟩
    rintro y ⟨-, -, h | h | h⟩
    · exact h.2 rfl
    · exact nomatch h.2
    · exact nomatch h.2
  have hasym : ¬ ActualGroundingAsymmetric rootedCycle () := fun h =>
    h (some false) (some true) ⟨trivial, trivial⟩ ⟨trivial, trivial⟩
      (Or.inr (Or.inl ⟨rfl, rfl⟩)) (Or.inr (Or.inr ⟨rfl, rfl⟩))
  refine ⟨?_, trivial, fun _ _ _ _ _ _ hg => hg, hasym, fun hWF => hasym
    (TruthCore.Causality.NecessaryConcreteRouteBridge.actualGroundingAsymmetricOfWF _ _ hWF),
    ⟨some false, some true, (), (), trivial, trivial, fun _ _ => trivial, fun _ _ => trivial,
      trivial, Or.inr (Or.inl ⟨rfl, rfl⟩), trivial, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩⟩
  intro S hS hNoRoot x hx
  cases x with
  | none => exact hNoRoot none hx hroot
  | some b =>
    exact hNoRoot none (hS.2 (some b) none hx ⟨trivial, trivial, Or.inl ⟨rfl, nofun⟩⟩) hroot

theorem attenuationSatisfiable : AttenuationSatisfiable := by
  refine ⟨inferInstance, fun _ _ => 0, fun _ => 1, fun _ => 1, 0, 1, le_rfl, zero_lt_one,
    zero_le_one, fun _ _ => le_rfl, fun _ => zero_le_one, fun _ => le_rfl,
    fun _ => summable_zero,
    ?_, ?_, ?_, ?_, ?_, fun _ => zero_lt_one⟩
  · intro v; simp
  · intro v; simp
  · intro v; simp
  · intro v u h; exact absurd h (lt_irrefl 0)
  · intro u _ y hy; exact hy.2.2

theorem mediateFoundationControl : MediateFoundationControl := by
  refine ⟨?_, ⟨trivial, trivial⟩, ?_⟩
  · intro hC
    refine hC (fun x => ∃ n, x = some n) ⟨fun _ _ => ⟨trivial, trivial⟩, ?_⟩ ?_ (some 0) ⟨0, rfl⟩
    · rintro x y ⟨n, rfl⟩ ⟨-, -, k, rfl, -⟩
      exact ⟨k+1, rfl⟩
    · rintro x ⟨n, rfl⟩ hr
      exact hr.2 (some (n+1)) ⟨trivial, trivial, n, rfl, rfl⟩
  · rintro y ⟨-, -, n, -, h⟩
    exact nomatch h

theorem abstractSupplierControl : AbstractSupplierControl := by
  refine ⟨?_, ?_, ?_⟩
  · intro S hS _ x hx
    cases x with
    | none => exact (hS.1 none hx).1 rfl
    | some n =>
      have h0 := hS.2 (some n) none hx trivial (Or.inl ⟨rfl, nofun⟩)
      exact (hS.1 none h0).1 rfl
  · intro h
    exact h (some 0) none ⟨nofun, trivial⟩ trivial (Or.inl ⟨rfl, nofun⟩) rfl
  · intro hC
    refine hC (fun x => ∃ n, x = some n) ⟨?_, ?_⟩ ?_ (some 0) ⟨0, rfl⟩
    · rintro x ⟨n, rfl⟩
      exact ⟨nofun, trivial⟩
    · rintro x y ⟨n, rfl⟩ ⟨hy, -, h | ⟨k, rfl, -⟩⟩
      · exact absurd h.1 hy
      · exact ⟨k+1, rfl⟩
    · rintro x ⟨n, rfl⟩ hr
      exact hr.2 (some (n+1)) ⟨nofun, trivial, Or.inr ⟨n, rfl, rfl⟩⟩

theorem controls : Controls :=
  ⟨limitGrounderControl, pureRegressControl, rootedCycleControl, attenuationSatisfiable,
    mediateFoundationControl, abstractSupplierControl⟩

end TruthCore.Results.Causality.ClosedGroundingRoots
