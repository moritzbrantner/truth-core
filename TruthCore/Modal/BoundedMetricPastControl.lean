import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia

namespace TruthCore.Modal.BoundedMetricPast
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- A mathematical interval with an included now=1, no first moment in the
existing PastIsInfinite sense, and clock age always in [0,1). Clock units are
stipulated; physical realization and time parametrization remain open. -/
def BoundedMetricPastControl : Prop :=
  ∃ now : Set.Ioc (0 : ℝ) 1,
    now.val = 1 ∧
    PastIsInfinite (fun s t : Set.Ioc (0 : ℝ) 1 => s.val < t.val) now ∧
    ¬ PastIsFinite (fun s t : Set.Ioc (0 : ℝ) 1 => s.val < t.val) now ∧
    ∀ t : Set.Ioc (0 : ℝ) 1, 0 ≤ now.val - t.val ∧ now.val - t.val < 1
end TruthCore.Modal.BoundedMetricPast
