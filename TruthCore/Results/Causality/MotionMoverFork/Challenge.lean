import TruthCore.Causality.MotionMoverFork

namespace TruthCore.Results.Causality.MotionMoverFork
open TruthCore.Causality.MotionMoverFork
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Latin.Aquinas.SummaTheologiae

theorem anotherGivesSomething {B R : Type} (moves : B → B → R → Prop) :
    AnotherGivesSomething moves := by
  sorry

theorem physicalGivesBroad {B R : Type} (physical : R → Prop) (moved : B → R → Prop) :
    PhysicalGivesBroad physical moved := by
  sorry

theorem anotherAnyGivesSomethingAny {B R : Type} (moves : B → B → R → Prop) :
    AnotherAnyGivesSomethingAny moves := by
  sorry

theorem moverFork {B R : Type} (moves accidental : B → B → R → Prop)
    (h : AccidentalHasPerSeMover moves accidental) : MoverForkSound moves accidental := by
  sorry

theorem broadFromPhysicalAndResidual {B R : Type} (physical residual : R → Prop)
    (moved : B → R → Prop) (moves : B → B → R → Prop)
    (hp : EveryPhysicalMotionHasAPerSeMoverReading physical moved moves)
    (hr : ResidualHasMover residual moved moves)
    (hc : MotionCoverage physical residual moved) : ReducedOnlyByAMoverReading moved moves := by
  sorry

theorem motionFork {B R : Type} (physical residual : R → Prop)
    (moved : B → R → Prop) (moves : B → B → R → Prop)
    (hp : EveryPhysicalMotionHasAPerSeMoverReading physical moved moves)
    (hr : ResidualHasMover residual moved moves)
    (hc : MotionCoverage physical residual moved) : MotionForkSound physical moved moves := by
  sorry

theorem controls : Controls := by
  sorry
end TruthCore.Results.Causality.MotionMoverFork
