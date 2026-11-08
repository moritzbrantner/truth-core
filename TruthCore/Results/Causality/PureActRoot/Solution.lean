module

public import TruthCore.Causality.PureActRoot
public import TruthCore.Results.Causality.PureActThisness.Solution
public import TruthCore.Results.Causality.PureIndiscernibility.Solution
public import TruthCore.Results.Causality.WholeRosterRootEquivalence.Solution

@[expose] public section

namespace TruthCore.Results.Causality.PureActRoot
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork (ActualRoot)
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Causality.PureActThisness
open TruthCore.Causality.PureIndiscernibility
open TruthCore.Causality.PureActRoot
open TruthCore.Case.Catholicism
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- Under the re-indexing, first-mover status is exactly actual rootness. -/
theorem firstIffRoot {W B : Type} (m : Profile W B) (w : W) (x : B) :
    IsFirstUnmovedMover (rootMoved m w) (rootMoves m w) x ↔ ActualRoot m w x :=
  ⟨fun h => match h.1 with | ⟨_, _, hr⟩ => hr,
   fun hr => ⟨⟨x, (), hr⟩, fun _ hn => hn hr⟩⟩

theorem everyOfRoot {W B D : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop)
    (h : ActualRootHasEveryPureDetermination m w Has Pure) :
    FirstMoverHasEveryPureDetermination (rootMoved m w) (rootMoves m w) Has Pure :=
  fun f hf => h f ((firstIffRoot m w f).mp hf)

theorem pureOfRoot {W B D : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop)
    (h : ActualRootDeterminationsArePure m w Has Pure) :
    FirstMoverDeterminationsArePure (rootMoved m w) (rootMoves m w) Has Pure :=
  fun f hf => h f ((firstIffRoot m w f).mp hf)

theorem thisOfRoot {W B D : Type} (m : Profile W B) (w : W) (Has : B → D → Prop)
    (h : ActualRootHasRealThisness m w Has) :
    FirstMoverHasRealThisness (rootMoved m w) (rootMoves m w) Has :=
  fun f hf => h f ((firstIffRoot m w f).mp hf)

/-- Existence from the whole-roster helper, uniqueness from any at-most-one
fact about the re-indexed first movers. -/
theorem uniqueOfAtMostOne {W B : Type} (m : Profile W B) (w : W)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hOne : AtMostOneFirstUnmovedMover (rootMoved m w) (rootMoves m w)) :
    UniqueNecessaryActualRootAt m w :=
  match TruthCore.Results.Causality.WholeRosterFoundation.necessaryActualRoot
      m w hPop hWhole hDep hEM with
  | ⟨n, hr, hn⟩ => ⟨n, hr, hn, fun x hx =>
      hOne x n ((firstIffRoot m w x).mpr hx) ((firstIffRoot m w n).mpr hr)⟩

theorem uniqueRootFromRealThisness {W B D : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hEvery : ActualRootHasEveryPureDetermination m w Has Pure)
    (hPure : ActualRootDeterminationsArePure m w Has Pure)
    (hThis : ActualRootHasRealThisness m w Has) :
    UniqueNecessaryActualRootAt m w :=
  uniqueOfAtMostOne m w hPop hWhole hDep hEM
    (TruthCore.Results.Causality.PureActThisness.uniqueFromRealThisness
      (rootMoved m w) (rootMoves m w) Has Pure
      (everyOfRoot m w Has Pure hEvery) (pureOfRoot m w Has Pure hPure)
      (thisOfRoot m w Has hThis))

theorem uniqueRootFromPureIndiscernibility {W B D : Type} (m : Profile W B) (w : W)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hPop : InhabitedConcreteAt m.ontic m.concrete w)
    (hWhole : WholeRosterNotTrapped m w)
    (hDep : EveryContingentGroundedAt m w) (hEM : ExcludedMiddle)
    (hEvery : ActualRootHasEveryPureDetermination m w Has Pure)
    (hPure : ActualRootDeterminationsArePure m w Has Pure)
    (hBridge : PurelyDeterminedIndiscerniblesIdentical Has Pure) :
    UniqueNecessaryActualRootAt m w :=
  uniqueOfAtMostOne m w hPop hWhole hDep hEM
    (TruthCore.Results.Causality.PureIndiscernibility.uniqueFromPureIndiscernibility
      (rootMoved m w) (rootMoves m w) Has Pure
      (everyOfRoot m w Has Pure hEvery) (pureOfRoot m w Has Pure hPure) hBridge)

section Controls
open TruthCore.Causality.PureActRoot.Control
open TruthCore.Causality.NecessaryConcreteRouteBridge (oneWorld oneWorld_dep)
open TruthCore.Results.Causality.WholeRosterRootEquivalence (wholeRosterOfRoot)

theorem twoRootsRoot (b : Bool) : ActualRoot twoRoots () b :=
  ⟨⟨trivial, trivial⟩, fun _ h => h.2.2⟩

theorem oneRootTrue : ActualRoot oneRoot () true :=
  ⟨⟨trivial, trivial⟩, fun _ h => Bool.noConfusion h.2.2.2⟩

theorem oneRootOnly (x : Bool) (h : ActualRoot oneRoot () x) : x = true :=
  Bool.rec (motive := fun b => ActualRoot oneRoot () b → b = true)
    (fun h => (h.2 true ⟨trivial, trivial, rfl, rfl⟩).elim) (fun _ => rfl) x h

theorem twoRootsBackground : Background twoRoots :=
  ⟨⟨true, trivial, trivial⟩, wholeRosterOfRoot twoRoots () ⟨true, twoRootsRoot true⟩,
    oneWorld_dep _⟩

theorem twoRootsNotUnique : ¬ UniqueNecessaryActualRootAt twoRoots () :=
  fun ⟨_, _, _, hall⟩ =>
    Bool.noConfusion ((hall true (twoRootsRoot true)).trans (hall false (twoRootsRoot false)).symm)

theorem thisReal : ActualRootHasRealThisness twoRoots () thisHas :=
  fun r _ => ⟨Sum.inr r, rfl, fun _ h => h⟩

theorem onlyTrueBridge : PurelyDeterminedIndiscerniblesIdentical onlyTrue (fun _ => True) :=
  fun x y _ h =>
    Bool.rec (motive := fun y => (x = true ↔ y = true) → x = y)
      (fun h' => Bool.rec (motive := fun x => (x = true ↔ false = true) → x = false)
        (fun _ => rfl) (fun h'' => Bool.noConfusion (h''.mp rfl)) x h')
      (fun h' => h'.mpr rfl) y (h ())

theorem emptyControl :
    ¬ InhabitedConcreteAt empty.ontic empty.concrete () ∧
    WholeRosterNotTrapped empty () ∧ EveryContingentGroundedAt empty () ∧
    ActualRootHasEveryPureDetermination empty () (fun _ (_ : Unit) => True) (fun _ => True) ∧
    ActualRootDeterminationsArePure empty () (fun _ (_ : Unit) => True) (fun _ => True) ∧
    ActualRootHasRealThisness empty () (fun _ (_ : Unit) => True) ∧
    PurelyDeterminedIndiscerniblesIdentical (fun (_ : Empty) (_ : Unit) => True) (fun _ => True) ∧
    ¬ UniqueNecessaryActualRootAt empty () := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; obtain ⟨e, _⟩ := h; exact nomatch e
  · intro h; obtain ⟨x, _⟩ := h; exact nomatch x.1
  · intro e; exact nomatch e
  · intro e; exact nomatch e
  · intro e; exact nomatch e
  · intro e; exact nomatch e
  · intro e; exact nomatch e
  · intro h; obtain ⟨e, _⟩ := h; exact nomatch e

theorem controls : Certificate := by
  refine ⟨⟨twoRootsBackground, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, ?_, ?_,
      twoRootsNotUnique⟩,
    ⟨twoRootsBackground, ?_, ?_, thisReal, ?_, twoRootsNotUnique⟩,
    ⟨twoRootsBackground, ?_, fun _ _ _ _ => trivial, thisReal, ?_, twoRootsNotUnique⟩,
    emptyControl,
    ⟨⟨⟨true, trivial, trivial⟩, wholeRosterOfRoot oneRoot () ⟨true, oneRootTrue⟩,
      oneWorld_dep _⟩, fun r hr _ _ => oneRootOnly r hr, fun _ _ _ _ => trivial,
      fun r hr => ⟨(), oneRootOnly r hr, fun y hy => hy.trans (oneRootOnly r hr).symm⟩,
      onlyTrueBridge,
      ⟨true, oneRootTrue, fun _ _ => trivial, fun x hx => oneRootOnly x hx⟩⟩⟩
  · intro h
    obtain ⟨_, _, honly⟩ := h true (twoRootsRoot true)
    exact Bool.noConfusion (honly false trivial)
  · intro h
    exact Bool.noConfusion (h true false (fun _ _ => trivial) (fun _ => Iff.rfl))
  · intro r _ d hp
    exact Sum.rec (motive := fun d => actOnly d → thisHas r d)
      (fun _ _ => trivial) (fun _ h => h.elim) d hp
  · intro h
    exact h true (twoRootsRoot true) (Sum.inr true) rfl
  · intro x _ hpure _
    exact (hpure (Sum.inr x) rfl).elim
  · intro h
    exact Bool.noConfusion (h true (twoRootsRoot true) (Sum.inr false) trivial)
  · intro x y _ h
    exact ((h (Sum.inr x)).mp rfl).symm

end Controls
end TruthCore.Results.Causality.PureActRoot
