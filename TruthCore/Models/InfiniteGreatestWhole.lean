import TruthCore.Models.QuartaViaDegreeFork
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Minimal
import Mathlib.Tactic.Linarith

/-! #696: regions are sets of mathematical points, ordered by inclusion.
This is neither an order of being nor evidence of actual physical infinity.
First-coordinate extent uses the ordinary real order, a different order from
inclusion on regions. No norm, topology or outer-boundary property is claimed. -/
namespace TruthCore.Models.InfiniteGreatestWhole
open TruthCore.Latin.Aquinas.SummaTheologiae

abbrev Point := Fin 3 → ℝ
abbrev Region := Set Point

def whole : Region := Set.univ
def origin : Point := fun _ => 0
def unitPoint : Point := fun _ => 1
def leftRegion : Region := {origin}
def rightRegion : Region := {unitPoint}

def coordinates (s : Region) : Set ℝ := (fun p : Point => p 0) '' s

/-- Domain membership in this contrast fixture, not possession of esse or a
source-attributed equation of extension, being, goodness and perfection. -/
def inAct (_ : Region) (_ : Unit) : Prop := True
def moreIn (_ : Unit) (s t : Region) : Prop := t ⊂ s

/-- A formal omission assignment. Calling it a cause, ground or explanatory
priority does not supply an interpreted physical/metaphysical relation. -/
def emptyPriority (_ _ : Region) : Prop := False

/-- The infinite point-set is greatest in the infinite family of all regions;
that family is order-bounded, although the whole's coordinate extent is not.
The same fixed geometry with no priority edges violates maximum-causes-all. -/
def RegionControl : Prop :=
  IsGreatest (Set.univ : Set Region) whole ∧ whole.Infinite ∧
  (Set.univ : Set Region).Infinite ∧
  BddAbove (Set.univ : Set Region) ∧ ¬ BddAbove (coordinates whole) ∧
  HomogeneousScaleReading inAct moreIn () ∧
  IsMaximalIn inAct moreIn () whole ∧
  ¬ QuartaViaNoMaximalDegree moreIn () ∧
  (∀ c x, ¬ emptyPriority c x) ∧
  ¬ CausesAllInGenus inAct (fun c x _ => emptyPriority c x) () whole ∧
  ¬ MaximumInBeingCausesAllBeingsReading inAct moreIn
      (fun c x _ => emptyPriority c x) () ∧
  ∀ s, BddAbove (coordinates s) → s ≠ whole

abbrev OpenDegree := {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}
def openMore (_ : Unit) (x y : OpenDegree) : Prop := y < x

/-- A bounded real interval with an unattained least upper bound and no
maximal member. No-maximal-degree therefore does not mean metric unbounded. -/
def OpenIntervalControl : Prop :=
  IsLUB (Set.Ioo (0 : ℝ) 1) 1 ∧ 1 ∉ Set.Ioo (0 : ℝ) 1 ∧
  BddAbove (Set.Ioo (0 : ℝ) 1) ∧
  QuartaViaNoMaximalDegree openMore () ∧ ¬ ∃ m : OpenDegree, IsMax m

/-- On a restricted family of two incomparable singleton regions, both are
maximal but neither is greatest. The family restriction is explicit. -/
def IncomparableControl : Prop :=
  leftRegion ≠ rightRegion ∧
  Maximal (fun s : Region => s ∈ ({leftRegion, rightRegion} : Set Region)) leftRegion ∧
  Maximal (fun s : Region => s ∈ ({leftRegion, rightRegion} : Set Region)) rightRegion ∧
  ¬ IsGreatest ({leftRegion, rightRegion} : Set Region) leftRegion ∧
  ¬ IsGreatest ({leftRegion, rightRegion} : Set Region) rightRegion

/-- The new infinite-greatest and bounded/no-top cases compose with the exact
old finite-top and Nat-ascent witnesses, not restatements of their proofs.
This is a mathematical order/omission certificate, not the Fourth Way. -/
def Certificate : Prop :=
  RegionControl ∧ OpenIntervalControl ∧ IncomparableControl ∧
  TruthCore.Models.QuartaViaDegreeFork.BranchWitnesses

end TruthCore.Models.InfiniteGreatestWhole
