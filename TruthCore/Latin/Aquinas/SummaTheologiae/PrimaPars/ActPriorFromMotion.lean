import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPotencyTheory
import TruthCore.Alternatives.NightCosmogony

/-!
Can act's simple priority (ST I q.3 a.1, `ActSimplyPriorToPotencyReading`) be
derived over the existing act/potency predicates from the theory of motion
(#352)? The Codex review of #374 named a route: if every potency is being
actualized, and an actual mover is simply prior to what it moves, then the
*prima via*'s "whatever is moved has a mover" and "a mover is in act" give
every potency a prior being in act.

This module states the one premise of that route that the case does not
already have (`EveryPotencyIsBeingActualizedReading`), the weaker priority
that the route yields without it (`ActPriorToActualizedPotencyReading`), and
the formal facts that decide between them (`ActPriorFromMotionFacts`). The
mover-priority bridge is the existing unattributed
`NightCosmogony.ActualMoverIsSimplyPriorReading`; *Physics* III.1's buildable
(`Physics.SomePotencyNotBeingActualizedReading`) is the sourced rival of the
new premise. No predicate is defined: all are fields of `ActPotencyModel`.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

open TruthCore.Alternatives.NightCosmogony (ActualMoverIsSimplyPriorReading)
open TruthCore.Greek.Aristotle.Physics (SomePotencyNotBeingActualizedReading)

universe u v

/-- Open premise, unattributed: every potency is being actualized. Whatever is
in potency in a respect is being moved (reduced to act) in that respect.

No source states it. Aquinas' own premise says the converse (*nihil movetur,
nisi secundum quod est in potentia*, `MovedOnlyAsInPotencyReading`), and his
statement of act's priority explicitly does not make every potency a present
being-moved (`ActSimplyPriorToPotencyReading`). Aristotle denies it: a
buildable is in potency without being built (*Physics* III.1, 201b8-9,
`SomePotencyNotBeingActualizedReading`). It is recorded only as the premise
that the motion route to act's priority needs. -/
def EveryPotencyIsBeingActualizedReading {Being : Sort u} {Respect : Sort v}
    (InPotency MovedIn : Being → Respect → Prop) : Prop :=
  ∀ x r, InPotency x r → MovedIn x r

/-- Act is simply prior to every potency that is being actualized: whatever is
in potency in a respect *and being moved in it* is simply posterior to some
being in act in that respect.

This is `ActSimplyPriorToPotencyReading` restricted to potencies being reduced
to act, the potencies of which Aquinas' reason (*quod est in potentia, non
reducitur in actum nisi per ens actu*) speaks. It says nothing about a potency
that is not being actualized. -/
def ActPriorToActualizedPotencyReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency MovedIn : Being → Respect → Prop)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ x r, InPotency x r → MovedIn x r → ∃ y, InAct y r ∧ PriorSimply y x

namespace ActPotencyModel

variable (M : ActPotencyModel)

/-- Every potency is being actualized (the route's new premise). -/
def EveryPotencyActualized : Prop :=
  EveryPotencyIsBeingActualizedReading M.InPotency M.MovedIn

/-- An actual mover of another's potency is simply prior to it (the open
bridge `STMT-ACTUAL-MOVER-IS-SIMPLY-PRIOR`). -/
def MoverPrior : Prop :=
  ActualMoverIsSimplyPriorReading M.InAct M.InPotency M.MovesIn M.PriorSimply

/-- Act is simply prior to every potency being actualized. -/
def ActPriorActualized : Prop :=
  ActPriorToActualizedPotencyReading M.InAct M.InPotency M.MovedIn M.PriorSimply

/-- Some potency is not being actualized (*Physics* III.1, 201b8-9). -/
def DormantPotency : Prop :=
  SomePotencyNotBeingActualizedReading M.InPotency M.MovedIn

end ActPotencyModel

open ActPotencyModel in
/-- Formal facts about deriving act's simple priority from motion.

1. **The route is valid.** Every potency being actualized, whatever is moved
   having a mover, every mover being in act, non-simultaneity and the actual
   mover's priority together entail act's simple priority. Non-simultaneity
   is what makes the mover another being: a self-mover would be in act and in
   potency in the same respect.
2. **Each of the five premises is needed.** Dropping any one leaves a model of
   the other four in which some potency has no prior being in act.
3. **It is not vacuous.** All five hold in a model in which something is moved
   and something is in potency.
4. **Without the new premise the route still yields priority for potencies
   being actualized**, from the other four.
5. **That weaker priority does not do the root's work.** There is a model of
   every *prima via* premise (sensible motion, moved only as in potency,
   has a mover, mover in act, non-simultaneity, second movers, well-founded per
   se series), the mover-priority bridge, the weaker priority and *Physics*
   III.1's dormant potency, in which a first mover moved by none is a first
   being (nothing else is simply prior to it) and is in potency in some
   respect. ST I q.3 a.1's second proof applies act's priority to exactly such
   a being, which is not being moved, so the restricted priority is vacuous for
   it.
6. **The new premise contradicts *Physics* III.1's dormant potency.** -/
def ActPriorFromMotionFacts : Prop :=
  (∀ M : ActPotencyModel, M.EveryPotencyActualized → M.HasMover → M.MoverInAct →
      M.NonSimultaneity → M.MoverPrior → M.ActPrior) ∧
  (¬ ∀ M : ActPotencyModel, M.HasMover → M.MoverInAct →
      M.NonSimultaneity → M.MoverPrior → M.ActPrior) ∧
  (¬ ∀ M : ActPotencyModel, M.EveryPotencyActualized → M.MoverInAct →
      M.NonSimultaneity → M.MoverPrior → M.ActPrior) ∧
  (¬ ∀ M : ActPotencyModel, M.EveryPotencyActualized → M.HasMover →
      M.NonSimultaneity → M.MoverPrior → M.ActPrior) ∧
  (¬ ∀ M : ActPotencyModel, M.EveryPotencyActualized → M.HasMover → M.MoverInAct →
      M.MoverPrior → M.ActPrior) ∧
  (¬ ∀ M : ActPotencyModel, M.EveryPotencyActualized → M.HasMover → M.MoverInAct →
      M.NonSimultaneity → M.ActPrior) ∧
  (∃ M : ActPotencyModel, M.EveryPotencyActualized ∧ M.HasMover ∧ M.MoverInAct ∧
      M.NonSimultaneity ∧ M.MoverPrior ∧ M.Sense ∧ ∃ x r, M.InPotency x r) ∧
  (∀ M : ActPotencyModel, M.HasMover → M.MoverInAct → M.NonSimultaneity →
      M.MoverPrior → M.ActPriorActualized) ∧
  (∃ M : ActPotencyModel, M.Sense ∧ M.Regress ∧ M.MovedInPotency ∧ M.HasMover ∧
      M.MoverInAct ∧ M.NonSimultaneity ∧ M.SecondMovers ∧ M.MoverPrior ∧
      M.ActPriorActualized ∧ M.DormantPotency ∧
      ∃ f, ((∃ x r, M.MovesIn f x r) ∧ ∀ r, ¬ M.MovedIn f r) ∧
        IsFirstBeing M.PriorSimply f ∧ ¬ PureAct M.InPotency f) ∧
  (∀ M : ActPotencyModel, M.EveryPotencyActualized → ¬ M.DormantPotency)

end TruthCore.Latin.Aquinas.SummaTheologiae
