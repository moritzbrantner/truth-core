import TruthCore.Greek.Aristotle.Physics.BookV.Chapter3

namespace TruthCore.Greek.Aristotle.Physics

/-- A motion is called one in several ways because one itself is said in several ways,
in Aristotle, *Physics* V.4, 227b3.

Source: Aristotle, *Physics* V.4, 227b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MotionSaidOneInSeveralWaysReading
    (MotionSaidOneInSeveralWays : Prop) : Prop :=
  MotionSaidOneInSeveralWays

/-- Motion is generically one according to its category in Aristotle, *Physics* V.4,
227b4-6: every locomotion is generically one with every locomotion, while alteration
and locomotion differ in genus.

Source: Aristotle, *Physics* V.4, 227b4-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenericUnityOfMotionFollowsCategoryReading
    (AnyLocomotionsGenericallyOne
      AlterationAndLocomotionGenericallyOne : Prop) : Prop :=
  AnyLocomotionsGenericallyOne ∧ ¬ AlterationAndLocomotionGenericallyOne

/-- Motion is specifically one when it is generically one and occurs in an indivisible
species in Aristotle, *Physics* V.4, 227b7-12. Thus every whitening is specifically one
with every whitening, while whitening and blackening differ specifically.

Source: Aristotle, *Physics* V.4, 227b7-12 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SpecificUnityRequiresIndivisibleSpeciesReading
    (GenericallyOne InSameIndivisibleSpecies SpecificallyOne : Prop) : Prop :=
  GenericallyOne ∧ InSameIndivisibleSpecies ∧ SpecificallyOne

/-- When something is both genus and species, its motion may be specifically one in a
qualified but not unqualified way in Aristotle, *Physics* V.4, 227b12-15. Learning is
the example when knowledge is a species of apprehension and a genus of sciences.

Source: Aristotle, *Physics* V.4, 227b12-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def GenusSpeciesYieldsQualifiedSpecificUnityReading
    (KindIsBothGenusAndSpecies SpecificallyOneQualifiedly
      SpecificallyOneUnqualifiedly : Prop) : Prop :=
  KindIsBothGenusAndSpecies ∧ SpecificallyOneQualifiedly ∧
    ¬ SpecificallyOneUnqualifiedly

/-- Repetition by one subject from the same source to the same goal does not suffice
for specific unity of motion in Aristotle, *Physics* V.4, 227b15-20. A specifically
different path makes circular and rectilinear motion, or rolling and walking, different
motions.

Source: Aristotle, *Physics* V.4, 227b15-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PathSpeciesDifferentiatesMotionDespiteSameTerminiReading
    (SameSubjectSourceAndGoal PathSpecificallyDifferent
      MotionsSpecificallyOne : Prop) : Prop :=
  SameSubjectSourceAndGoal ∧ PathSpecificallyDifferent ∧ ¬ MotionsSpecificallyOne

end TruthCore.Greek.Aristotle.Physics
