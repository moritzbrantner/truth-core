import TruthCore.Greek.Aristotle.Physics.BookI.Chapter4

namespace TruthCore.Greek.Aristotle.Physics

/--
Doxographical consensus reported in Aristotle, *Physics* I.5, 188a19-26: despite their
differences, earlier accounts make contraries principles in one form or another.

This records Aristotle's classification of the earlier thinkers, not endorsement of each
thinker's particular pair of contraries.

Source: Aristotle, *Physics* I.5, 188a19-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EarlierThinkersUseContraryPrinciplesReading
    (EarlierAccountsUseContrariesAsPrinciples : Prop) : Prop :=
  EarlierAccountsUseContrariesAsPrinciples

/--
Structural conditions Aristotle gives for first principles in *Physics* I.5, 188a26-30:
they are not derived from one another or from something prior, while other things are
derived from them.

The conjunction preserves both the independence and explanatory-source conditions.

Source: Aristotle, *Physics* I.5, 188a26-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FirstPrinciplesIndependentAndGenerativeReading
    (PrinciplesNotDerivedFromOneAnotherOrAnother : Prop)
    (OtherThingsDerivedFromPrinciples : Prop) : Prop :=
  PrinciplesNotDerivedFromOneAnotherOrAnother ∧ OtherThingsDerivedFromPrinciples

/--
Constraint on natural change in Aristotle, *Physics* I.5, 188a31-188b8: a thing does not
naturally act on, suffer from, arise from, or pass into just anything at random. Apparent
exceptions may hold only incidentally because of an accompanying attribute.

Source: Aristotle, *Physics* I.5, 188a31-188b8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalChangeNotFromOrIntoRandomThingsReading
    (NaturalChangeFromOrIntoRandomThingsAsSuch : Prop) : Prop :=
  ¬ NaturalChangeFromOrIntoRandomThingsAsSuch

/--
Immediate source alternatives in Aristotle, *Physics* I.5, 188b8-20: what comes to be or
passes away does so from or into a contrary or an intermediate state.

The disjunction does not yet collapse intermediates into contraries; that is a separate
premise and inference in the corpus.

Source: Aristotle, *Physics* I.5, 188b8-20 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def BecomingFromContraryOrIntermediateReading
    (FromContrary : Prop)
    (FromIntermediate : Prop) : Prop :=
  FromContrary ∨ FromIntermediate

/--
Intermediate states are derived from contraries in Aristotle, *Physics* I.5, 188b20-26,
illustrated by colours derived from black and white.

The implication is scoped to the role of intermediates in the chapter's account of natural
becoming, not asserted as a modern universal theory of every ordered domain.

Source: Aristotle, *Physics* I.5, 188b20-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def IntermediatesDerivedFromContrariesReading
    (FromIntermediate : Prop)
    (FromContraries : Prop) : Prop :=
  FromIntermediate → FromContraries

/--
Conclusion of Aristotle's reasoned transition in *Physics* I.5, 188b20-26: natural becoming
is from a contrary or from something derived from contraries.

The formal support from the preceding alternatives and intermediate premise is represented
separately as an inference application and mechanically verified argument.

Source: Aristotle, *Physics* I.5, 188b20-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalBecomingFromContraryOrContrariesReading
    (FromContrary : Prop)
    (FromContraries : Prop) : Prop :=
  FromContrary ∨ FromContraries

/--
Analogical comparison in Aristotle, *Physics* I.5, 188b27-189a4: predecessor principles
differ in their selected pairs yet are the same in an analogical respect, with some pairs
wider and some narrower in explanatory extent.

Source: Aristotle, *Physics* I.5, 188b27-189a4 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContraryPrinciplesAnalogicallySameReading
    (PrinciplesDifferInSelectedPairs : Prop)
    (PrinciplesAnalogicallySame : Prop) : Prop :=
  PrinciplesDifferInSelectedPairs ∧ PrinciplesAnalogicallySame

/--
Epistemic ordering distinguished in Aristotle, *Physics* I.5, 189a5-9: universal pairs are
more knowable in the order of account, while particular pairs are more familiar to sense.

This preserves Aristotle's two relative orders of knowability rather than treating one class
as simply more knowable without qualification.

Source: Aristotle, *Physics* I.5, 189a5-9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UniversalExplanatoryParticularSensibleKnowabilityReading
    (UniversalsMoreKnowableByAccount : Prop)
    (ParticularsMoreKnowableBySense : Prop) : Prop :=
  UniversalsMoreKnowableByAccount ∧ ParticularsMoreKnowableBySense

/--
Closing conclusion of Aristotle, *Physics* I.5, 189a9-10: the principles of natural things
must be contraries.

This is recorded as Aristotle's chapter conclusion. The mechanically verified result in this
batch is limited to the narrower preceding derivation about natural becoming.

Source: Aristotle, *Physics* I.5, 189a9-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NaturalPrinciplesMustBeContrariesReading
    (NaturalPrinciplesMustBeContraries : Prop) : Prop :=
  NaturalPrinciplesMustBeContraries

end TruthCore.Greek.Aristotle.Physics
