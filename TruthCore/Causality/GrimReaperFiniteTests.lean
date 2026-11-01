import TruthCore.Causality.GrimReaper
import Mathlib.Data.Finset.Lattice.Fold

/-! Source-free finite-test control for the exact existing Reaper rule.
Only the tested indices are finite; each tested clause still quantifies over
the entire unbounded natural-number tail. This is not a finite schedule and
does not assert causal powers, possible worlds or metaphysical realizability. -/
namespace TruthCore.Causality.GrimReaperFiniteTests

/-- Every finite selection of the complete infinite-tail clauses has a total
action assignment on Nat, although no assignment satisfies all the clauses.
The assignment may vary with the selected finite set. This is a mathematical
compatibility control, not a first-order compactness failure or a claim about
the modal assembly principle used by Koons. -/
def FiniteTestsWithoutGlobalSchedule : Prop :=
  (∀ indices : Finset Nat, ∃ acts : Nat → Prop,
    ∀ n ∈ indices, acts n ↔ ∀ m, n < m → ¬ acts m) ∧
  NoFirstGrimReaperSchedule

end TruthCore.Causality.GrimReaperFiniteTests
