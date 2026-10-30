import TruthCore.Models.ActPotencyRemaining
import TruthCore.Greek.Aristotle.Physics.Typed.Motion

/-! The registered NRegress interpretation is reused unchanged: a moves b in k,
and b moves a in h. Each recipient is in potency in the incoming respect and
each mover is actual in the outgoing respect. Thus the two respects differ,
but a cycle and the lack of a globally unmoved mover remain possible in this
encoding. No temporal sequence or metaphysical possibility is asserted. -/
namespace TruthCore.Models.RespectAlternatingMotionCycle

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Greek.Aristotle.Physics.Typed
open TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels

abbrev model := TruthCore.Models.ActPotencyRemaining.NRegress.model

/-- One existing interpretation jointly satisfies all four local premises,
has an alternating two-cycle, has no globally unmoved mover, and violates the
separate well-founded per-se-regress premise. The conclusion of a local
same-respect path exclusion is therefore not general cycle rejection. -/
def JointWitness : Prop :=
  MovingIsInTheMovedReading model.MovesIn model.MovedIn ∧
  MovedOnlyAsInPotencyReading model.MovedIn model.InPotency ∧
  MovesOnlyAsInActReading model.MovesIn model.InAct ∧
  NotActAndPotencyInSameRespectReading model.InAct model.InPotency ∧
  (∃ a b r s, a ≠ b ∧ r ≠ s ∧ model.MovesIn a b r ∧ model.MovesIn b a s) ∧
  (¬ ∃ f, (∃ x r, model.MovesIn f x r) ∧ ∀ r, ¬ model.MovedIn f r) ∧
  ¬ NoInfinitePerSeMoverSeriesReading model.MovesAsMoved

theorem inMoved : MovingIsInTheMovedReading model.MovesIn model.MovedIn := by
  intro y x r h
  cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial

theorem moverActual : MovesOnlyAsInActReading model.MovesIn model.InAct := by
  intro y x r h
  cases y <;> cases x <;> cases r <;> first | exact False.elim h | exact trivial

theorem alternatingCycle :
    ∃ a b r s, a ≠ b ∧ r ≠ s ∧ model.MovesIn a b r ∧ model.MovesIn b a s :=
  ⟨B2.a, B2.b, R2.k, R2.h, (by intro h; cases h),
    (by intro h; cases h), trivial, trivial⟩

/-- The old certificate negates a double-negated existential. An actual
existential witness would yield that double negation, so it too is impossible
in this same interpretation; no excluded middle is used. -/
theorem noGloballyUnmovedMover :
    ¬ ∃ f, (∃ x r, model.MovesIn f x r) ∧ ∀ r, ¬ model.MovedIn f r :=
  fun h => TruthCore.Models.ActPotencyRemaining.NRegress.evaluation5
    (fun hNoWitness => hNoWitness h)

theorem jointWitness : JointWitness :=
  ⟨inMoved, TruthCore.Models.ActPotencyRemaining.NRegress.evaluation1,
    moverActual, TruthCore.Models.ActPotencyRemaining.NRegress.evaluation3,
    alternatingCycle, noGloballyUnmovedMover,
    TruthCore.Models.ActPotencyRemaining.NRegress.evaluation6⟩

end TruthCore.Models.RespectAlternatingMotionCycle
