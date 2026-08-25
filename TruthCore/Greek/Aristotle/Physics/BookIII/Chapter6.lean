import TruthCore.Greek.Aristotle.Physics.BookIII.Chapter5

namespace TruthCore.Greek.Aristotle.Physics

/--
Dialectical transition in Aristotle, *Physics* III.6, 206a8-14: denying infinity in every
sense would force unacceptable consequences for time, divisibility of magnitude, and number.

The three consequences are packaged as a source-level proposition. The statement does not
itself decide which positive sense of infinity survives; the next reading makes that
distinction.

Source: Aristotle, *Physics* III.6, 206a8-14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DenyingInfiniteEntirelyHasImpossibleConsequencesReading
    (DenyInfiniteEntirely : Prop)
    (ImpossibleConsequences : Prop) : Prop :=
  DenyInfiniteEntirely → ImpossibleConsequences

/--
Aristotle's governing distinction in *Physics* III.6, 206a8-18: the infinite exists in one
sense and does not exist in another, corresponding to the distinction between potential and
complete/actual being and to infinity by addition or division.

The proposition parameters keep those modes abstract rather than identifying them with a
modern set-theoretic notion of infinity.

Source: Aristotle, *Physics* III.6, 206a8-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteExistsInOneSenseNotAnotherReading
    (ExistsPotentially : Prop)
    (ExistsAsCompletedActual : Prop) : Prop :=
  ExistsPotentially ∧ ¬ ExistsAsCompletedActual

/--
Magnitude-specific reading of Aristotle, *Physics* III.6, 206a16-18: magnitude is not
actually infinite, but it is infinite with respect to division; hence its infinity is
potential in the relevant sense.

This statement preserves the source's joint classification rather than treating potential
infinity as a future completed magnitude.

Source: Aristotle, *Physics* III.6, 206a16-18 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MagnitudePotentiallyInfiniteByDivisionReading
    (InfiniteByDivision : Prop)
    (ActuallyInfiniteMagnitude : Prop) : Prop :=
  InfiniteByDivision ∧ ¬ ActuallyInfiniteMagnitude

/--
Clarification in Aristotle, *Physics* III.6, 206a18-25: potential infinity is not potential
in the way a possible statue is expected eventually to become an actual statue. There will
not be a completed actual infinite corresponding to the potential infinite.

Source: Aristotle, *Physics* III.6, 206a18-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PotentialInfiniteNotFutureCompletedActualReading
    (PotentialInfinite : Prop)
    (WillBecomeCompletedActualInfinite : Prop) : Prop :=
  PotentialInfinite → ¬ WillBecomeCompletedActualInfinite

/--
General successive-mode reading of Aristotle, *Physics* III.6, 206a27-33: infinity exists
through always being able to take another item or stage; what is taken at any stage is finite,
while another is always available.

`Stage` and the two predicates remain abstract so the same weak pattern can cover magnitude,
time, and generations without identifying their distinct modes.

Source: Aristotle, *Physics* III.6, 206a27-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteAsAlwaysAnotherFiniteStageReading
    {Stage : Type}
    (IsTakenStage : Stage → Prop)
    (IsFinite : Stage → Prop)
    (HasFurtherStage : Stage → Prop) : Prop :=
  (∀ stage, IsTakenStage stage → IsFinite stage) ∧
    (∀ stage, IsTakenStage stage → HasFurtherStage stage)

/--
Mode distinction in Aristotle, *Physics* III.6, 206a25-206b3: the successive infinity of
time and generations involves earlier stages passing away, whereas in the division of a
magnitude the parts taken persist. The common "always another" structure therefore does not
make these cases identical in mode.

Source: Aristotle, *Physics* III.6, 206a25-206b3 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteModesDifferAcrossTimeGenerationMagnitudeReading
    (TimeSuccessionByPassingAway : Prop)
    (GenerationSuccessionByPassingAway : Prop)
    (MagnitudeDivisionPartsPersist : Prop) : Prop :=
  TimeSuccessionByPassingAway ∧
    GenerationSuccessionByPassingAway ∧
    MagnitudeDivisionPartsPersist

/--
Conditional used in Aristotle's restriction on additive infinity in *Physics* III.6,
206b17-25: a potential infinity by addition that could exceed every determinate magnitude
would require an actually infinite sensible body of the kind already rejected in III.5.

Source: Aristotle, *Physics* III.6, 206b17-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnboundedAdditivePotentialRequiresActualInfiniteBodyReading
    (UnboundedAdditivePotential : Prop)
    (ActuallyInfiniteSensibleBody : Prop) : Prop :=
  UnboundedAdditivePotential → ActuallyInfiniteSensibleBody

/--
Conclusion of Aristotle's argument in *Physics* III.6, 206b17-25: there is no potential
infinity by addition which exceeds every determinate magnitude. Additive potential infinity
survives only in the inverse manner tied to division.

Source: Aristotle, *Physics* III.6, 206b17-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoUnboundedAdditivePotentialReading
    (UnboundedAdditivePotential : Prop) : Prop :=
  ¬ UnboundedAdditivePotential

/--
Definition-like reading in Aristotle, *Physics* III.6, 206b33-207a14: a quantity is infinite
when, however much has been taken, there is always something further outside what has already
been taken.

The relation is kept iterative rather than reified as a completed infinite whole.

Source: Aristotle, *Physics* III.6, 206b33-207a14 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteAsAlwaysSomethingOutsideReading
    {Stage : Type}
    (Taken : Stage → Prop)
    (SomethingFurtherOutside : Stage → Prop) : Prop :=
  ∀ stage, Taken stage → SomethingFurtherOutside stage

/--
Material/potential-whole reading in Aristotle, *Physics* III.6, 207a18-29: the infinite is
better understood as matter for the completeness of magnitude and as potentially whole, not
as an actually complete whole that contains everything; qua infinite it is contained rather
than containing.

The predicates remain source-relative to avoid importing later matter/form commitments into
a general theory of mathematical infinity.

Source: Aristotle, *Physics* III.6, 207a18-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteAsMaterialPotentialWholeReading
    (IsMatterForMagnitudeCompletion : Prop)
    (IsPotentiallyWhole : Prop)
    (IsActuallyCompleteWhole : Prop)
    (ContainsAsInfinite : Prop) : Prop :=
  IsMatterForMagnitudeCompletion ∧
    IsPotentiallyWhole ∧
    ¬ IsActuallyCompleteWhole ∧
    ¬ ContainsAsInfinite

end TruthCore.Greek.Aristotle.Physics
