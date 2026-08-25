import TruthCore.Greek.Aristotle.Physics.BookIII.Chapter4

namespace TruthCore.Greek.Aristotle.Physics

/--
Dialectical premise in Aristotle, *Physics* III.5, 204a8-16: if the infinite were a
separable substance in its own right rather than an attribute of magnitude or plurality, it
would be indivisible.

The conclusion follows from the local division Aristotle draws: what is divisible is a
magnitude or plurality. The statement does not claim that every substance is indivisible.

Source: Aristotle, *Physics* III.5, 204a8-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SeparateInfiniteSubstanceWouldBeIndivisibleReading
    (SeparateInfiniteSubstance : Prop)
    (Indivisible : Prop) : Prop :=
  SeparateInfiniteSubstance → Indivisible

/--
Companion premise in Aristotle, *Physics* III.5, 204a8-16: the infinite relevant to the
physical inquiry is not the merely privative sense exemplified by a voice being "invisible";
it is the untraversable/unbounded sense and therefore is not the indivisible item produced by
the separable-substance hypothesis.

Source: Aristotle, *Physics* III.5, 204a8-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RelevantInfiniteNotIndivisibleReading
    (Indivisible : Prop) : Prop :=
  ¬ Indivisible

/--
Conclusion of Aristotle's opening argument in *Physics* III.5, 204a8-16: there is no
separable substance which is itself the infinite in the sense relevant to this inquiry.

This does not deny infinity as an attribute or its later potential mode of being.

Source: Aristotle, *Physics* III.5, 204a8-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoSeparateInfiniteSubstanceReading
    (SeparateInfiniteSubstance : Prop) : Prop :=
  ¬ SeparateInfiniteSubstance

/--
Attribute/principle distinction from Aristotle, *Physics* III.5, 204a16-29: if infinity
belongs to something as an attribute, infinity qua infinity is not itself the underlying
principle; rather the subject to which it belongs would be the candidate principle.

Source: Aristotle, *Physics* III.5, 204a16-29 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfinityAsAttributeNotItselfPrincipleReading
    {Subject : Type}
    (HasInfinity : Subject → Prop)
    (IsUnderlyingPrinciple : Subject → Prop)
    (InfinityItselfIsPrinciple : Prop) : Prop :=
  (∃ subject, HasInfinity subject ∧ IsUnderlyingPrinciple subject) →
    ¬ InfinityItselfIsPrinciple

/--
Physical classification in Aristotle, *Physics* III.5, 204b10-22: an actually infinite
sensible body cannot be a compound body made from the finite set of contrary elements under
discussion, because an infinite amount of one would overwhelm a finite contrary while making
each element infinite is also excluded.

The details of elemental potency remain in the source interpretation rather than being turned
into a universal modern law of mixtures.

Source: Aristotle, *Physics* III.5, 204b10-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteSensibleBodyNotCompoundReading
    (InfiniteSensibleBodyIsCompound : Prop) : Prop :=
  ¬ InfiniteSensibleBodyIsCompound

/--
Companion classification in Aristotle, *Physics* III.5, 204b22-205a7: an actually infinite
sensible body cannot instead be one simple body, whether one of the familiar elements or a
separate sensible element alongside them.

Source: Aristotle, *Physics* III.5, 204b22-205a7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteSensibleBodyNotSimpleReading
    (InfiniteSensibleBodyIsSimple : Prop) : Prop :=
  ¬ InfiniteSensibleBodyIsSimple

/--
Natural-place constraint from Aristotle, *Physics* III.5, 205a7-206a7: the hypothesis of an
actually infinite sensible body conflicts with the differentiated proper places and natural
motions belonging to sensible bodies.

`ConflictsWithProperPlaceOrder` is intentionally primitive. This avoids importing a modern
spatial model while preserving the role played by up/down, centre/extremity, rest, and
natural locomotion in Aristotle's general demonstration.

Source: Aristotle, *Physics* III.5, 205a7-206a7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfiniteSensibleBodyConflictsWithProperPlaceReading
    (ActuallyInfiniteSensibleBody : Prop)
    (ConflictsWithProperPlaceOrder : Prop) : Prop :=
  ActuallyInfiniteSensibleBody → ConflictsWithProperPlaceOrder

/--
Conclusion of Aristotle, *Physics* III.5, 206a7: there is no sensible body which is actually
infinite.

The claim is deliberately about actual infinity of sensible body. It does not pre-empt the
potential infinity Aristotle introduces in III.6.

Source: Aristotle, *Physics* III.5, 206a7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NoActuallyInfiniteSensibleBodyReading
    (ActuallyInfiniteSensibleBody : Prop) : Prop :=
  ¬ ActuallyInfiniteSensibleBody

end TruthCore.Greek.Aristotle.Physics
