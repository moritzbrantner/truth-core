import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaVia
import TruthCore.Greek.Aristotle.MetaphysicsIII3

/-!
Which *genus* the *quarta via* needs (issue #340).

ST I q.2 a.3 co. says *Quod autem dicitur maxime tale in aliquo genere, est
causa omnium quae sunt illius generis*, and applies it to being. Aristotle
(*Metaphysics* III.3, 998b22-27) and Aquinas himself (ST I q.3 a.5 co.) say that
being is not a genus. Both cannot use *genus* in the same sense unless the
*quarta via* fails at being.

The corpus reading `MaximumInGenusCausesAllInGenusReading` already takes
*genus* broadly (`DEF-GENUS-BROAD`): any perfection `r` admitting more and
less, as heat in the example (heat is a quality, not a strict genus of the hot
things). This file adds the strict alternative only for contrast
(`DEF-GENUS-STRICT`): the principle restricted to perfections that are genera
in Aristotle's sense. It is not attributed to Aquinas.

To let Aristotle's predication vocabulary speak about perfections, a
perfection (`Respect`) is identified with the predicable that says it: `IsGenus
r`, `DifferentiaOf d r` and `SaidOf t s` take respects, and *being* (`ens`) is
the respect `esse`.

Two formal facts, both premise-free and recorded as statements:

* `StrictGenusReadingDoesNotYieldQuartaVia`: on the strict reading, together
  with Aristotle's three premises for being-not-a-genus, the *quarta via*'s
  conclusion does not follow;
* `BroadGenusReadingCompatibleWithBeingNotAGenus`: on the broad reading, all
  four *quarta via* premises, its conclusion and Aristotle's three premises
  hold together in one model that has a genuine strict genus with a
  differentia. So being-not-a-genus does not refute the broad premise.
-/

namespace TruthCore.Latin.Aquinas.SummaTheologiae

open TruthCore.Greek.Aristotle.Metaphysics

universe u v

/-- Contrast reading of the genus principle with *genus* in the strict sense:
what is maximal in a perfection that is a genus causes that perfection in every
other thing that has it.

Not attributed to Aquinas: the *quarta via* applies the principle to being and
the example is heat, neither a genus in this sense. Recorded as the reading an
objector gives the sentence (`DISAMB-GENUS`). -/
def MaximumInStrictGenusCausesAllInGenusReading {Being : Sort u}
    {Respect : Sort v} (IsGenus : Respect → Prop)
    (InAct : Being → Respect → Prop)
    (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) : Prop :=
  ∀ r, IsGenus r → ∀ m, IsMaximumIn InAct MoreIn r m →
    CausesAllInGenus InAct CausesIn r m

/-- Formal fact: the strict reading of the genus principle, with the other three
*quarta via* premises and Aristotle's three premises for being-not-a-genus (at
`ens = esse`), does not yield that something maximal in being causes the being
of every other being. -/
def StrictGenusReadingDoesNotYieldQuartaVia : Prop :=
  ¬ ∀ (Being Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (IsGenus : Respect → Prop) (DifferentiaOf SaidOf : Respect → Respect → Prop)
      (bonum verum nobile esse : Respect),
      GradesFoundInThingsReading MoreIn bonum verum nobile →
      GradesByApproachToAMaximumReading InAct MoreIn →
      MostTrueIsMostBeingReading InAct MoreIn verum esse →
      MaximumInStrictGenusCausesAllInGenusReading IsGenus InAct MoreIn CausesIn →
      EveryGenusHasADifferentiaReading IsGenus DifferentiaOf →
      DifferentiaeAreBeingsReading IsGenus DifferentiaOf SaidOf esse →
      GenusNotSaidOfOwnDifferentiaeReading IsGenus DifferentiaOf SaidOf →
      MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse

/-- Formal fact: the broad reading of the genus principle (the corpus reading),
the other three *quarta via* premises, the *quarta via*'s conclusion, and
Aristotle's three premises for being-not-a-genus (at `ens = esse`) are jointly
satisfiable, in a model where some respect is a strict genus with a
differentia (so the strict vocabulary is not empty). -/
def BroadGenusReadingCompatibleWithBeingNotAGenus : Prop :=
  ∃ (Being Respect : Type)
      (InAct : Being → Respect → Prop)
      (MoreIn : Respect → Being → Being → Prop)
      (CausesIn : Being → Being → Respect → Prop)
      (IsGenus : Respect → Prop) (DifferentiaOf SaidOf : Respect → Respect → Prop)
      (bonum verum nobile esse : Respect),
      GradesFoundInThingsReading MoreIn bonum verum nobile ∧
      GradesByApproachToAMaximumReading InAct MoreIn ∧
      MostTrueIsMostBeingReading InAct MoreIn verum esse ∧
      MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn ∧
      EveryGenusHasADifferentiaReading IsGenus DifferentiaOf ∧
      DifferentiaeAreBeingsReading IsGenus DifferentiaOf SaidOf esse ∧
      GenusNotSaidOfOwnDifferentiaeReading IsGenus DifferentiaOf SaidOf ∧
      (∃ g d, IsGenus g ∧ DifferentiaOf d g) ∧
      MaximeEnsCausesBeingOfAllReading InAct MoreIn CausesIn esse

end TruthCore.Latin.Aquinas.SummaTheologiae
