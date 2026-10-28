import Mathlib.Data.Int.Order.Basic
import TruthCore.Modal.TemporalHistory
import TruthCore.Causality.BruteFoundationBoundary
import TruthCore.Models.PSR

/-! Two history extensions of existing ontologies, with explicit now-slice
coherence. No existing existence, cause or ground assignment is changed.
The first uses the old rival's child, not its ungrounded root. The second
uses only the old PSR model's ontology; explanation labels do no work here.
-/
namespace TruthCore.Models.TemporalHistoryControls
open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.BruteFoundationBoundary

/-- The same present individuals occupy every integer time within each world. -/
def everlasting : History Bool (Bool × Bool) Int where
  ontic := boundaryRival.ontic
  IsAt := fun w x _ => boundaryRival.ontic.ExistsAt w x
  now := 0

/-- The original actually present target first appears at zero in each world.
The absent candidate stays absent. This stipulates no timeless eternity. -/
def beginning : History Bool Bool Int where
  ontic := PSR.Intrinsic.model.ontic
  IsAt := fun w x t => PSR.Intrinsic.model.ontic.ExistsAt w x ∧ 0 ≤ t
  now := 0

/-- One fixed everlasting history contains a contingent target with a distinct
actual concrete cause and ground. A different fixed history contains a necessary
target beginning at zero. Neither control asserts a global relation between
causation and grounding, a metaphysical possibility, or timeless Eternal. -/
def JointControls : Prop :=
  CoherentAtNow everlasting ∧
  EverlastingAt everlasting false (false, true) ∧
  ContingentAt everlasting.ontic false (false, true) ∧
  (∃ y, y ≠ (false, true) ∧ boundaryRival.concrete y ∧
    everlasting.ontic.ExistsAt false y ∧
    everlasting.ontic.Causes false y (false, true) ∧
    boundaryRival.grounds false y (false, true)) ∧
  CoherentAtNow beginning ∧
  BeginsAt beginning false false 0 ∧
  NecessaryAt beginning.ontic false false ∧
  ¬ ContingentAt beginning.ontic false false

end TruthCore.Models.TemporalHistoryControls
