import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPriorFromMotion
import TruthCore.Latin.Aquinas.InMetaphysicam.BookIX

/-!
Does the priority in substance of *Metaphysics* Θ.8, 1050b6-19, as Aquinas
reads it (*In Metaph.* IX, lect. 9), give act's simple priority (ST I q.3 a.1,
`ActSimplyPriorToPotencyReading`) over potencies that are not being actualized
(#352)? The motion route (`ActPriorFromMotionFacts`) reaches only potencies
being actualized; Θ.8's argument does not speak of motion at all.

The argument read here: every potency is of the contradictory, so whatever is
in potency in a respect can fail to be so (`PotencyIsOfContradictionReading`);
incorruptible beings are prior in substance to corruptible ones
(`IncorruptiblePriorInSubstanceReading`) and are, as such, in act
(`IncorruptibleIsInActReading`). Two further hypotheses are needed and are
not formalized as readings: an incorruptible being exists (the passages
presuppose incorruptible heavens, 1050b22-28 and lect. 9 n. 10-13, where n. 13
makes their perpetuity depend on divine will), and priority in substance is
simple priority (`PriorInSubstanceIsSimpleReading`), which no source read here
states. The facts
below show what the argument yields with them: act's simple priority over
potency *in substance* (`ActPriorInSubstanceReading`), and not over potency in
a respect other than substance, which Aquinas expressly allows an
incorruptible being (lect. 9 n. 6).
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

open TruthCore.Latin.Aquinas.InMetaphysicam

universe u v

/-- Open bridge, unattributed: what is prior in substance (*prius substantia et
perfectione*) is simply prior. No source read for #352 identifies the two
relations; `DEF-SIMPLE-PRIORITY` characterizes simple priority by the
reduction of potency to act, not by perfection. -/
def PriorInSubstanceIsSimpleReading {Being : Sort u}
    (PriorInSubstance PriorSimply : Being → Being → Prop) : Prop :=
  ∀ y x, PriorInSubstance y x → PriorSimply y x

/-- Act is simply prior to potency in substance: whatever is in potency in the
respect of being is simply posterior to some being in act in that respect.

This is `ActSimplyPriorToPotencyReading` restricted to the one respect `esse`.
It says nothing about a potency in a place, quantity or quality. -/
def ActPriorInSubstanceReading {Being : Sort u} {Respect : Sort v}
    (InAct InPotency : Being → Respect → Prop) (esse : Respect)
    (PriorSimply : Being → Being → Prop) : Prop :=
  ∀ x, InPotency x esse → ∃ y, InAct y esse ∧ PriorSimply y x

/-- Formal facts about deriving act's simple priority from the incorruptible
beings of *Met.* Θ.8 and *In Metaph.* IX, lect. 9.

1. **A being that cannot fail to be in any respect is pure act**, given that
   every potency is of the contradictory. No source read here says that the
   first being cannot fail to be in any respect.
2. **The substance route is valid.** Every potency being of the contradictory,
   the priority in substance of the incorruptible, the act of the
   incorruptible, the existence of an incorruptible being and the
   identification of priority in substance with simple priority together
   entail act's simple priority over potency in substance. No premise about
   motion or about potencies being actualized is used.
3. **Each of the five is needed.** Dropping any one leaves a model of the
   other four in which something in potency in substance has no prior being in
   act in substance.
4. **It is not vacuous.** All five hold, with non-simultaneity, in a model in
   which something is in potency in substance.
5. **It reaches the first being's substance.** With non-simultaneity, the
   restricted priority excludes that a first being (nothing else is simply
   prior to it) is in potency in substance.
6. **It does not reach the root's use.** There is a model of every *prima via*
   premise (sensible motion, moved only as in potency, has a mover, mover in
   act, non-simultaneity, second movers, well-founded per se series), of
   actuality only insofar as being, of the mover-priority bridge, of act's
   priority over potencies being actualized (the motion route's yield) and of
   all five premises of item 2, in which act's simple priority fails: a first
   mover moved by none is a first being, is incorruptible simply, and is in
   potency in a respect other than substance in which it is not moved. The
   five readings do not exclude this: lect. 9 n. 6 allows potency in a respect
   (*secundum quid*) in simply incorruptible beings, with moved bodies (sun,
   moon) as its examples. It does not speak of a first mover; lect. 8 n. 11
   calls the first mover *in actu tantum*, which no reading here formalizes. -/
def ActPriorFromIncorruptibleFacts : Prop :=
  (∀ (Being Respect : Type) (InPotency CanFailToBe : Being → Respect → Prop),
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      ∀ f, (∀ r, ¬ CanFailToBe f r) → PureAct InPotency f) ∧
  (∀ (Being Respect : Type) (esse : Respect)
      (InAct InPotency CanFailToBe : Being → Respect → Prop)
      (PriorInSubstance PriorSimply : Being → Being → Prop),
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      IncorruptiblePriorInSubstanceReading CanFailToBe esse PriorInSubstance →
      IncorruptibleIsInActReading InAct CanFailToBe esse →
      (∃ e, IncorruptibleSimply CanFailToBe esse e) →
      PriorInSubstanceIsSimpleReading PriorInSubstance PriorSimply →
      ActPriorInSubstanceReading InAct InPotency esse PriorSimply) ∧
  (¬ ∀ (Being Respect : Type) (esse : Respect)
      (InAct InPotency CanFailToBe : Being → Respect → Prop)
      (PriorInSubstance PriorSimply : Being → Being → Prop),
      IncorruptiblePriorInSubstanceReading CanFailToBe esse PriorInSubstance →
      IncorruptibleIsInActReading InAct CanFailToBe esse →
      (∃ e, IncorruptibleSimply CanFailToBe esse e) →
      PriorInSubstanceIsSimpleReading PriorInSubstance PriorSimply →
      ActPriorInSubstanceReading InAct InPotency esse PriorSimply) ∧
  (¬ ∀ (Being Respect : Type) (esse : Respect)
      (InAct InPotency CanFailToBe : Being → Respect → Prop)
      (PriorInSubstance PriorSimply : Being → Being → Prop),
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      IncorruptibleIsInActReading InAct CanFailToBe esse →
      (∃ e, IncorruptibleSimply CanFailToBe esse e) →
      PriorInSubstanceIsSimpleReading PriorInSubstance PriorSimply →
      ActPriorInSubstanceReading InAct InPotency esse PriorSimply) ∧
  (¬ ∀ (Being Respect : Type) (esse : Respect)
      (InAct InPotency CanFailToBe : Being → Respect → Prop)
      (PriorInSubstance PriorSimply : Being → Being → Prop),
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      IncorruptiblePriorInSubstanceReading CanFailToBe esse PriorInSubstance →
      (∃ e, IncorruptibleSimply CanFailToBe esse e) →
      PriorInSubstanceIsSimpleReading PriorInSubstance PriorSimply →
      ActPriorInSubstanceReading InAct InPotency esse PriorSimply) ∧
  (¬ ∀ (Being Respect : Type) (esse : Respect)
      (InAct InPotency CanFailToBe : Being → Respect → Prop)
      (PriorInSubstance PriorSimply : Being → Being → Prop),
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      IncorruptiblePriorInSubstanceReading CanFailToBe esse PriorInSubstance →
      IncorruptibleIsInActReading InAct CanFailToBe esse →
      PriorInSubstanceIsSimpleReading PriorInSubstance PriorSimply →
      ActPriorInSubstanceReading InAct InPotency esse PriorSimply) ∧
  (¬ ∀ (Being Respect : Type) (esse : Respect)
      (InAct InPotency CanFailToBe : Being → Respect → Prop)
      (PriorInSubstance PriorSimply : Being → Being → Prop),
      PotencyIsOfContradictionReading InPotency CanFailToBe →
      IncorruptiblePriorInSubstanceReading CanFailToBe esse PriorInSubstance →
      IncorruptibleIsInActReading InAct CanFailToBe esse →
      (∃ e, IncorruptibleSimply CanFailToBe esse e) →
      ActPriorInSubstanceReading InAct InPotency esse PriorSimply) ∧
  (∃ (Being Respect : Type) (esse : Respect)
      (InAct InPotency CanFailToBe : Being → Respect → Prop)
      (PriorInSubstance PriorSimply : Being → Being → Prop),
      PotencyIsOfContradictionReading InPotency CanFailToBe ∧
      IncorruptiblePriorInSubstanceReading CanFailToBe esse PriorInSubstance ∧
      IncorruptibleIsInActReading InAct CanFailToBe esse ∧
      (∃ e, IncorruptibleSimply CanFailToBe esse e) ∧
      PriorInSubstanceIsSimpleReading PriorInSubstance PriorSimply ∧
      NotActAndPotencyInSameRespectReading InAct InPotency ∧
      ∃ x, InPotency x esse) ∧
  (∀ (Being Respect : Type) (esse : Respect)
      (InAct InPotency : Being → Respect → Prop) (PriorSimply : Being → Being → Prop),
      NotActAndPotencyInSameRespectReading InAct InPotency →
      ActPriorInSubstanceReading InAct InPotency esse PriorSimply →
      ∀ f, IsFirstBeing PriorSimply f → ¬ InPotency f esse) ∧
  (∃ (M : ActPotencyModel) (CanFailToBe : M.Being → M.Respect → Prop)
      (PriorInSubstance : M.Being → M.Being → Prop),
      M.Sense ∧ M.Regress ∧ M.MovedInPotency ∧ M.HasMover ∧ M.MoverInAct ∧
      M.NonSimultaneity ∧ M.SecondMovers ∧ M.ActualityAsBeing ∧ M.MoverPrior ∧
      M.ActPriorActualized ∧
      PotencyIsOfContradictionReading M.InPotency CanFailToBe ∧
      IncorruptiblePriorInSubstanceReading CanFailToBe M.esse PriorInSubstance ∧
      IncorruptibleIsInActReading M.InAct CanFailToBe M.esse ∧
      (∃ e, IncorruptibleSimply CanFailToBe M.esse e) ∧
      PriorInSubstanceIsSimpleReading PriorInSubstance M.PriorSimply ∧
      ¬ M.ActPrior ∧
      ∃ f, ((∃ x r, M.MovesIn f x r) ∧ ∀ r, ¬ M.MovedIn f r) ∧
        IsFirstBeing M.PriorSimply f ∧ IncorruptibleSimply CanFailToBe M.esse f ∧
        ∃ r, r ≠ M.esse ∧ M.InPotency f r ∧ ¬ M.MovedIn f r)

end TruthCore.Latin.Aquinas.SummaTheologiae
