import TruthCore.Greek.Aristotle.Physics.BookIII.Chapter6

namespace TruthCore.Greek.Aristotle.Physics

/--
Directional-asymmetry reading of Aristotle, *Physics* III.7, 207b1-10: number has a lower
bound at the indivisible unit while every assigned number can be exceeded upward; magnitude
has the converse structure relevant here, remaining indefinitely divisible toward smaller
magnitudes while not growing into an actually infinite magnitude.

The four supplied propositions preserve Aristotle's directional comparison without importing
a modern construction of natural or real numbers.

Source: Aristotle, *Physics* III.7, 207b1-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NumberMagnitudeDirectionalAsymmetryReading
    (NumberHasIndivisibleMinimum : Prop)
    (EveryAssignedNumberCanBeExceeded : Prop)
    (MagnitudeIndefinitelyDivisible : Prop)
    (NoInfiniteMagnitudeByIncrease : Prop) : Prop :=
  NumberHasIndivisibleMinimum ∧
    EveryAssignedNumberCanBeExceeded ∧
    MagnitudeIndefinitelyDivisible ∧
    NoInfiniteMagnitudeByIncrease

/--
Bisection reading of Aristotle, *Physics* III.7, 207b10-15: the number of possible bisections
is infinite potentially, never as a separable permanent actuality; its infinity consists in
the continuing process.

Source: Aristotle, *Physics* III.7, 207b10-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BisectionInfinityPotentialNotActualReading
    (PotentiallyUnboundedBisections : Prop)
    (ActuallyCompletedInfiniteBisections : Prop)
    (SeparablePermanentInfinity : Prop) : Prop :=
  PotentiallyUnboundedBisections ∧
    ¬ ActuallyCompletedInfiniteBisections ∧
    ¬ SeparablePermanentInfinity

/--
Dependency reading of Aristotle, *Physics* III.7, 207b21-27: infinity in magnitude, motion,
and time is not one single nature predicated identically of each. Motion is called infinite
by reference to magnitude, and time by reference to motion.

Source: Aristotle, *Physics* III.7, 207b21-27 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfinityDependencyMagnitudeMotionTimeReading
    (OneIdenticalInfiniteNature : Prop)
    (MotionInfinityDependsOnMagnitude : Prop)
    (TimeInfinityDependsOnMotion : Prop) : Prop :=
  ¬ OneIdenticalInfiniteNature ∧
    MotionInfinityDependsOnMagnitude ∧
    TimeInfinityDependsOnMotion

/--
Mathematical-sufficiency reading of Aristotle, *Physics* III.7, 207b27-34: mathematical
proof does not require an actually infinite magnitude; it requires only that finite magnitude
can be extended or produced as far as the argument calls for.

This records Aristotle's methodological claim without asserting that all later mathematics
can be reconstructed under the same restriction.

Source: Aristotle, *Physics* III.7, 207b27-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MathematicsNeedsArbitraryFiniteNotActualInfiniteReading
    (ArbitraryFiniteExtensionAvailable : Prop)
    (RequiresActuallyInfiniteMagnitude : Prop) : Prop :=
  ArbitraryFiniteExtensionAvailable ∧ ¬ RequiresActuallyInfiniteMagnitude

/--
Causal classification in Aristotle, *Physics* III.7, 207b34-208a4: within the four-cause
scheme the infinite is a cause as matter; its being is characterized by privation, and its
underlying subject is the continuous and sensible. Qua infinite it is contained rather than
the containing boundary.

Source: Aristotle, *Physics* III.7, 207b34-208a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteMaterialCausePrivationReading
    (IsMaterialCause : Prop)
    (EssenceIsPrivation : Prop)
    (SubjectIsContinuousAndSensible : Prop)
    (IsContained : Prop)
    (ContainsRatherThanIsContained : Prop) : Prop :=
  IsMaterialCause ∧
    EssenceIsPrivation ∧
    SubjectIsContinuousAndSensible ∧
    IsContained ∧
    ¬ ContainsRatherThanIsContained

end TruthCore.Greek.Aristotle.Physics
