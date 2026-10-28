import TruthCore.Spacetime.BoostSimultaneity
namespace TruthCore.Results.Spacetime.BoostSimultaneity
open TruthCore.Spacetime.BoostSimultaneity

private theorem forwardCone (p : Event) (hp : FutureCone p) : FutureCone (boost p) := by
  rcases abs_le.mp hp with ⟨hl, hr⟩
  apply abs_le.mpr
  change -((5 * p.1 - 4 * p.2) / 3) ≤ (5 * p.2 - 4 * p.1) / 3 ∧
    (5 * p.2 - 4 * p.1) / 3 ≤ (5 * p.1 - 4 * p.2) / 3
  constructor <;> linarith

private theorem backwardCone (p : Event) (hp : FutureCone (boost p)) : FutureCone p := by
  rcases abs_le.mp hp with ⟨hl, hr⟩
  change -((5 * p.1 - 4 * p.2) / 3) ≤ (5 * p.2 - 4 * p.1) / 3 at hl
  change (5 * p.2 - 4 * p.1) / 3 ≤ (5 * p.1 - 4 * p.2) / 3 at hr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem unequalTimes : ¬ Simultaneous (boost origin) (boost separated) := by
  change ¬ (5 * (0 : ℝ) - 4 * 0) / 3 = (5 * 0 - 4 * 1) / 3
  norm_num

/-- Analyst 1+1 rational-boost control; physical/ontological adequacy remains open. -/
theorem controls : Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact boost.map_app p
  · intro p
    exact ⟨backwardCone p, forwardCone p⟩
  · intro p q
    change FutureCone (boost q - boost p) ↔ FutureCone (q - p)
    rw [← map_sub boost q p]
    exact ⟨backwardCone _, forwardCone _⟩
  · refine ⟨?_, ?_, rfl, unequalTimes⟩
    · intro h
      have hh := congrArg Prod.snd h
      norm_num [origin, separated] at hh
    · norm_num [origin, separated]
  · rintro ⟨P, ha, hb⟩
    exact unequalTimes ((hb origin separated).mp ((ha origin separated).mpr rfl))
  · refine ⟨Simultaneous, fun _ _ => Iff.rfl, ?_⟩
    intro h
    exact unequalTimes ((h origin separated).mp rfl)

end TruthCore.Results.Spacetime.BoostSimultaneity
