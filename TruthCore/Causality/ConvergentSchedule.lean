import Mathlib.Analysis.SpecificLimits.Basic
import TruthCore.Causality.Supertasks

/-!
# A convergent Zeno schedule for the abstract supertask order

`TruthCore.Causality.Supertasks` models a supertask's *order*: the stages
`SupertaskMoment.stage n` and a distinct `SupertaskMoment.limit` ordered by
`SupertaskPrecedes` (an omega-plus-one order). It carries no metric time.

This module assigns that same order real-valued clock times, using Mathlib's
real numbers, filters and unconditional sums instead of a hand-rolled limit
notion. Stage `n` begins at `1 - (1/2)^n`; it lasts `(1/2)^(n+1)`; the limit
endpoint sits at time `1`.

This is a **mathematical** model of a finite-duration schedule with infinitely
many stages. It does not assert that infinitely many distinct physical
operations can be carried out in finite time (the open SU-REAL bridge of
`docs/supertasks.md`, #318), nor that any output is attained at the endpoint.
-/

namespace TruthCore.Causality

open Filter Topology

/-- Clock time (in units of the whole schedule) at which stage `n` begins:
`1 - (1/2)^n`, so stage `0` begins at time `0`. -/
noncomputable def zenoStageTime (n : ℕ) : ℝ :=
  1 - (1 / 2 : ℝ) ^ n

/-- Duration of stage `n`: half of the time remaining before the endpoint,
`(1/2)^(n+1)`. -/
noncomputable def zenoStageDuration (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (n + 1)

/-- The clock reading of each moment of the abstract supertask order: stage
`n` is read at `zenoStageTime n` and the limit endpoint at time `1`. -/
noncomputable def zenoMomentTime : SupertaskMoment → ℝ
  | .stage n => zenoStageTime n
  | .limit => 1

/-- The convergent Zeno schedule, stated with Mathlib's notions of strict
monotonicity, convergence (`Tendsto … (𝓝 _)`) and unconditional summation
(`HasSum`):

1. later stages begin strictly later (`StrictMono`);
2. every stage begins before time `1`;
3. the stage times converge to the endpoint's time;
4. each stage's duration is exactly the gap to the next stage time;
5. the stage durations sum to `1`, the whole schedule's length;
6. the clock is an order embedding of the existing supertask order into the
   real line: `SupertaskPrecedes a b` holds exactly when `a` is read strictly
   before `b`.

Clause 6 ties the real-valued schedule to `SupertaskMoment` and
`SupertaskPrecedes`, the order used by `EndlessStagesWithStableEndpoint`,
rather than introducing a parallel stage vocabulary. -/
def ConvergentZenoSchedule : Prop :=
  StrictMono zenoStageTime ∧
    (∀ n, zenoStageTime n < 1) ∧
      Tendsto (fun n => zenoMomentTime (.stage n)) atTop
          (𝓝 (zenoMomentTime .limit)) ∧
        (∀ n, zenoStageTime (n + 1) - zenoStageTime n = zenoStageDuration n) ∧
          HasSum zenoStageDuration 1 ∧
            ∀ a b : SupertaskMoment,
              SupertaskPrecedes a b ↔ zenoMomentTime a < zenoMomentTime b

end TruthCore.Causality
