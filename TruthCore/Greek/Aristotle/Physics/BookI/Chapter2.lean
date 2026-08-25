import TruthCore.Greek.Aristotle.Physics.BookI.Chapter1

namespace TruthCore.Greek.Aristotle.Physics

/--
Initial logical space in Aristotle, *Physics* I.2, 184b15-25: the principles sought are one
or many; if one, motionless or moving; if many, finite or infinite in plurality.

The branches are kept as alternatives rather than assertions that any branch is true.

Source: Aristotle, *Physics* I.2, 184b15-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PrincipleAlternativesReading
    (OnePrinciple : Prop)
    (ManyPrinciples : Prop)
    (OneMotionless : Prop)
    (OneMoving : Prop)
    (ManyFinite : Prop)
    (ManyInfinite : Prop) : Prop :=
  (OnePrinciple ∨ ManyPrinciples) ∧
    (OnePrinciple → OneMotionless ∨ OneMoving) ∧
    (ManyPrinciples → ManyFinite ∨ ManyInfinite)

/--
Scope reading of Aristotle, *Physics* I.2, 184b25-185a12: investigating whether Being is
one and motionless in the Eleatic sense is not itself a question internal to natural science,
because it removes the principles from which the science proceeds.

Source: Aristotle, *Physics* I.2, 184b25-185a12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OneMotionlessBeingOutsidePhysicsReading
    (OneMotionlessBeingIsPhysicsQuestion : Prop) : Prop :=
  ¬ OneMotionlessBeingIsPhysicsQuestion

/--
Starting assumption of Aristotle, *Physics* I.2, 185a12-14: the physicist takes it as given
that all or at least some natural things are in motion, something Aristotle says is evident
from induction.

Source: Aristotle, *Physics* I.2, 185a12-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SomeNaturalThingsAreInMotionReading
    (SomeNaturalThingsAreInMotion : Prop) : Prop :=
  SomeNaturalThingsAreInMotion

/--
Disciplinary-boundary reading of Aristotle, *Physics* I.2, 185a14-20: a science is not
obliged to answer every arbitrary challenge, but the difficulties that arise falsely from its
own principles are properly its business.

Source: Aristotle, *Physics* I.2, 185a14-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ScienceAddressesPrincipleBasedDifficultiesReading
    (MustAnswerEveryDifficulty : Prop)
    (MustAnswerPrincipleBasedDifficulties : Prop) : Prop :=
  ¬ MustAnswerEveryDifficulty ∧ MustAnswerPrincipleBasedDifficulties

/--
Semantic distinction in Aristotle, *Physics* I.2, 185a20-185b5: "being" is said in more
than one way, including substance, quantity, and quality. Consequently an assertion that all
things are one must specify the sense of being involved.

Source: Aristotle, *Physics* I.2, 185a20-185b5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BeingHasSeveralSensesReading
    (SubstanceSense : Prop)
    (QuantitySense : Prop)
    (QualitySense : Prop) : Prop :=
  SubstanceSense ∧ QuantitySense ∧ QualitySense

/--
Parallel distinction in Aristotle, *Physics* I.2, 185b5-16: "one" can mean continuous,
indivisible, or one in definition/essence. These senses must not be silently conflated.

Source: Aristotle, *Physics* I.2, 185b5-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OneHasSeveralSensesReading
    (ContinuousSense : Prop)
    (IndivisibleSense : Prop)
    (SameDefinitionSense : Prop) : Prop :=
  ContinuousSense ∧ IndivisibleSense ∧ SameDefinitionSense

/--
First premise in Aristotle's continuous-One argument in *Physics* I.2, 185b5-16: if the
alleged One is one by continuity, it is divisible.

Source: Aristotle, *Physics* I.2, 185b5-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousOneImpliesDivisibleReading
    (OneByContinuity : Prop)
    (Divisible : Prop) : Prop :=
  OneByContinuity → Divisible

/--
Second premise in Aristotle's continuous-One argument in *Physics* I.2, 185b5-16: what is
divisible has a plurality of parts and so is many in that respect.

Source: Aristotle, *Physics* I.2, 185b5-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DivisibleImpliesManyReading
    (Divisible : Prop)
    (ManyInParts : Prop) : Prop :=
  Divisible → ManyInParts

/--
Conclusion of the continuous-One argument in Aristotle, *Physics* I.2, 185b5-16: if the
One is continuous, it is many in respect of its divisible parts.

This does not claim that continuity and plurality are contradictory simpliciter; Aristotle
later explicitly allows one and many in different non-opposed respects.

Source: Aristotle, *Physics* I.2, 185b5-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContinuousOneImpliesManyReading
    (OneByContinuity : Prop)
    (ManyInParts : Prop) : Prop :=
  OneByContinuity → ManyInParts

/--
Qualified one/many reading of Aristotle, *Physics* I.2, 185b25-186a3: the same thing can be
one and many in different respects—e.g. one subject with different definitions or a whole
with parts—provided the predicates are not opposites in the same respect. Aristotle also
distinguishes potential and actual unity.

Source: Aristotle, *Physics* I.2, 185b25-186a3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SameThingOneAndManyInNonOppositeRespectsReading
    (OneInOneRespect : Prop)
    (ManyInAnotherRespect : Prop)
    (RespectsAreOpposed : Prop) : Prop :=
  OneInOneRespect ∧ ManyInAnotherRespect ∧ ¬ RespectsAreOpposed

end TruthCore.Greek.Aristotle.Physics
