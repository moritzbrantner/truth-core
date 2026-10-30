import TruthCore.Science.ReadingSelfCertification
import TruthCore.Results.Science.MeasurementCalibration.Solution
import TruthCore.Results.Logic.CorrectionCriterion.Solution
import Mathlib.Tactic.Abel

namespace TruthCore.Results.Science.ReadingSelfCertification
open TruthCore.Science.ReadingSelfCertification

/-- The earlier calibration theorem supplies a profile with any chosen bias
and exactly the same complete readings. Unrestricted signals are essential. -/
private theorem compensate {X V : Type} [AddCommGroup V]
    (p : Profile X V) (d : V) :
    readings p = readings (fun x => p.1 x + p.2 - d, d) := by
  have shift : TruthCore.Science.MeasurementCalibration.OffsetShift
      p.1 (fun x => p.1 x + p.2 - d) p.2 d (p.2 - d) := by
    constructor
    · abel
    · intro x; abel
  exact funext ((TruthCore.Results.Science.MeasurementCalibration.certificate.1
    X V p.1 (fun x => p.1 x + p.2 - d) p.2 d).mpr ⟨p.2 - d, shift⟩)

/-- A zero-bias conclusion cannot be uniformly guaranteed by positive tests
of reading-only data; exact classification fails too. A supplied true signal
anchor removes this particular obstruction under constant bias. -/
theorem certificate : Certificate := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X V _ d nonzero Evidence derive test sound p positive
    let q : Profile X V := (fun x => p.1 x + p.2 - d, d)
    have same : derive (readings p) = derive (readings q) :=
      congrArg derive (compensate p d)
    have accurate : Accurate q := sound q (same ▸ positive)
    exact nonzero accurate
  · intro X V _ d nonzero Evidence derive exactCriterion
    let p : Profile X V := (fun _ => 0, 0)
    let q : Profile X V := (fun x => p.1 x + p.2 - d, d)
    have invariant :=
      (TruthCore.Results.Logic.CorrectionCriterion.characterization.1
        (Profile X V) Evidence (fun s => derive (readings s)) Accurate).mp exactCriterion
    have accurate : Accurate q :=
      (invariant p q (congrArg derive (compensate p d))).mp rfl
    exact nonzero accurate
  · intro X V _ x₀
    apply (TruthCore.Results.Logic.CorrectionCriterion.characterization.1
      (Profile X V) ((X → V) × V) (anchoredReadings x₀) Accurate).mpr
    intro p q same
    have readingsSame : TruthCore.Science.MeasurementCalibration.SameReadings
        p.1 q.1 p.2 q.2 := by
      intro x
      exact congrFun (congrArg Prod.fst same) x
    have anchorSame : p.1 x₀ = q.1 x₀ := congrArg Prod.snd same
    have biasesSame :=
      (TruthCore.Results.Science.MeasurementCalibration.certificate.2.1
        X V p.1 q.1 p.2 q.2 (p.1 x₀) x₀ readingsSame rfl anchorSame.symm).1
    change (p.2 = 0 ↔ q.2 = 0)
    rw [biasesSame]
  · refine ⟨((fun x => if x then 1 else 0), 0),
      ((fun x => if x then 0 else -1), 1), ?_, rfl, ?_, ?_, ?_, ?_⟩
    · funext x; cases x <;> decide
    · change ¬ ((1 : Int) = 0); decide
    · decide
    · intro x; cases x <;> decide
    · intro same
      have bad : (0 : Int) = -1 := congrArg Prod.snd same
      exact (by decide : (0 : Int) ≠ -1) bad

end TruthCore.Results.Science.ReadingSelfCertification
