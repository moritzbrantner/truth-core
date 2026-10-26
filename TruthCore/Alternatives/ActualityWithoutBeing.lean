import TruthCore.Alternatives.ActPotencyRegress
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPotencyTheory

/-!
The elimination attempt for the Meinongian rival of ST I q.4 a.1 ad 3 (#497).

The rival `ActualityWithoutBeingReading` ("something is in act in some respect
without being in act in the respect `esse`") is, in the shared vocabulary, the
contradictory of the premise `ActualityOnlyInsofarAsBeingReading`. So any
premise set that refutes the rival yields the premise (up to a double negation
that excluded middle removes), and the only inclusion-minimal refuting core in
this vocabulary is the premise itself. The other seven act/potency premises,
with sensible motion and the well-founded per se series, do not refute it.
-/

namespace TruthCore.Alternatives.ActualityWithoutBeing

open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Alternatives.ActPotencyRegress

/-- Formal fact (#497): the elimination of the rival `ActualityWithoutBeingReading`
reduces to the premise it rivals, and fails from the other act/potency premises.

1. The rival and the premise are jointly inconsistent: rival ∧ premise ⊢ False.
2. A refutation of the rival is exactly the double-negated premise: the rival
   fails iff whatever is in act in some respect is not *not* in act in `esse`.
   With excluded middle for `InAct x esse` this is the premise. So no premise set
   refutes the rival without (classically) entailing the premise.
3. Some `ActPotencyModel` satisfies sensible motion, the well-founded per se
   series, the other seven act/potency premises of #352 and the rival.

All three are about the formal encoding: carriers of `Type`, `InAct` and `esse`
as parameters with no further constraint. Item 3 is satisfiability of that
encoding, not metaphysical possibility, and says nothing about premise sets
outside the tested ones. -/
def ActualityWithoutBeingEliminationReducesToPremise : Prop :=
  (∀ (Being Respect : Type) (InAct : Being → Respect → Prop) (esse : Respect),
      ActualityWithoutBeingReading InAct esse →
        ActualityOnlyInsofarAsBeingReading InAct esse → False) ∧
  (∀ (Being Respect : Type) (InAct : Being → Respect → Prop) (esse : Respect),
      ¬ ActualityWithoutBeingReading InAct esse ↔
        ∀ x r, InAct x r → ¬ ¬ InAct x esse) ∧
  ∃ M : ActPotencyModel, M.Sense ∧ M.Regress ∧ M.NonSimultaneity ∧ M.ActPrior ∧
    M.GoodnessAsAct ∧ M.MoverInAct ∧ M.HasMover ∧ M.MovedInPotency ∧
    M.SecondMovers ∧ ActualityWithoutBeingReading M.InAct M.esse

end TruthCore.Alternatives.ActualityWithoutBeing
