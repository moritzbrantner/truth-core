import TruthCore.Greek.Aristotle.Physics.BookI.Chapter3

namespace TruthCore.Greek.Aristotle.Physics

/--
Doxographical structure in Aristotle, *Physics* I.4, 187a12-26: natural philosophers broadly
use two explanatory patterns—one underlying body differentiated by contraries such as rare
and dense, and contraries already contained in a mixture and separated out from it.

The conjunction records that Aristotle recognizes both patterns in his taxonomy; it does not
endorse either predecessor model as true.

Source: Aristotle, *Physics* I.4, 187a12-26 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def TwoPhysicalExplanatoryPatternsReading
    (OneSubstrateDifferentiatedByContraries : Prop)
    (ContrariesSegregatedFromMixture : Prop) : Prop :=
  OneSubstrateDifferentiatedByContraries ∧ ContrariesSegregatedFromMixture

/--
First premise in Aristotle's reconstruction of Anaxagoras's motivation in *Physics* I.4,
187a26-187b7: generation from absolute not-being is rejected.

This is reported as part of the attributed motivation for Anaxagoras's model, not as an
independent endorsement of every Anaxagorean conclusion.

Source: Aristotle, *Physics* I.4, 187a26-187b7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NothingFromAbsoluteNotBeingReading
    (NothingFromAbsoluteNotBeing : Prop) : Prop :=
  NothingFromAbsoluteNotBeing

/--
Second premise in Aristotle's reconstruction of Anaxagoras's motivation in *Physics* I.4,
187a26-187b7: contraries are observed to arise from one another.

Source: Aristotle, *Physics* I.4, 187a26-187b7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ContrariesComeFromOneAnotherReading
    (ContrariesComeFromOneAnother : Prop) : Prop :=
  ContrariesComeFromOneAnother

/--
Attributed Anaxagorean conclusion reconstructed by Aristotle in *Physics* I.4,
187a26-187b7: what emerges must already have been present imperceptibly in the mixture.

The support relation from the two preceding premises is represented separately in the corpus
as an inference application and argument rather than hidden in this statement declaration.

Source: Aristotle, *Physics* I.4, 187a26-187b7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AnaxagoreanEmergentThingsAlreadyPresentReading
    (EmergentThingsAlreadyPresent : Prop) : Prop :=
  EmergentThingsAlreadyPresent

/--
Predominance reading reported by Aristotle, *Physics* I.4, 187b2-7: on the Anaxagorean
account everything is mixed with everything, and a thing is named according to whichever
kind predominates in its mixture rather than being wholly pure of the others.

Source: Aristotle, *Physics* I.4, 187b2-7 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AnaxagoreanPredominantConstituentNamingReading
    (EverythingMixedInEverything : Prop)
    (NamedByPredominantConstituent : Prop) : Prop :=
  EverythingMixedInEverything ∧ NamedByPredominantConstituent

/--
First premise of Aristotle's epistemic objection in *Physics* I.4, 187b7-13: principles that
are infinite both in multitude and in kind are unknowable in the respects required for
knowing their quantity and quality.

`PrinciplesKnowable` is kept proposition-level so the claim does not presuppose a modern
formal theory of computability or cardinality.

Source: Aristotle, *Physics* I.4, 187b7-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def InfinitePrinciplesUnknowableReading
    (PrinciplesKnowable : Prop) : Prop :=
  ¬ PrinciplesKnowable

/--
Second premise of Aristotle's epistemic objection in *Physics* I.4, 187b7-13: scientific
knowledge of a composite requires knowing what its components are and how many there are.

Source: Aristotle, *Physics* I.4, 187b7-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompositeKnowledgeRequiresPrincipleKnowledgeReading
    (CompositeKnowable : Prop)
    (PrinciplesKnowable : Prop) : Prop :=
  CompositeKnowable → PrinciplesKnowable

/--
Conclusion of Aristotle's epistemic objection in *Physics* I.4, 187b7-13: a composite cannot
be scientifically known if its principles are unknowable because they are infinite in both
multitude and kind.

Source: Aristotle, *Physics* I.4, 187b7-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def CompositeFromInfinitePrinciplesNotKnowableReading
    (CompositeKnowable : Prop) : Prop :=
  ¬ CompositeKnowable

/--
Size objection in Aristotle, *Physics* I.4, 187b13-22: because animals and plants are not
indefinitely large or small, their genuine constituent parts such as flesh or bone cannot be
indefinitely large or small either.

The biological premise remains source-scoped; it is not promoted to a general mathematical
law about part-whole size.

Source: Aristotle, *Physics* I.4, 187b13-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def OrganicPartsNotIndefiniteInSizeReading
    (OrganicWholesHaveBoundedSize : Prop)
    (ConstituentPartsHaveBoundedSize : Prop) : Prop :=
  OrganicWholesHaveBoundedSize → ConstituentPartsHaveBoundedSize

/--
Exhaustion objection in Aristotle, *Physics* I.4, 187b22-35: the thesis that every finite
body contains every other kind as already-present constituents cannot be sustained by
indefinite repeated separation of finite constituents; either separation terminates, or the
finite body is made to contain an impossible infinite multitude of finite portions.

Source: Aristotle, *Physics* I.4, 187b22-35 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EverythingInEverythingExhaustionObjectionReading
    (EverythingAlreadyInEverything : Prop)
    (CompatibleWithFiniteExhaustion : Prop) : Prop :=
  EverythingAlreadyInEverything → ¬ CompatibleWithFiniteExhaustion

/--
Qualitative objection in Aristotle, *Physics* I.4, 188a5-13: affections such as colours and
states are inseparable from subjects, so complete separation cannot yield a free-standing
white or healthy item with no subject.

Source: Aristotle, *Physics* I.4, 188a5-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AffectionsNotSeparatelyExtractableReading
    (AffectionsAreInseparable : Prop)
    (CompleteQualitativeSeparationPossible : Prop) : Prop :=
  AffectionsAreInseparable → ¬ CompleteQualitativeSeparationPossible

/--
Closing methodological preference in Aristotle, *Physics* I.4, 188a13-17: against the
Anaxagorean infinity of principles, Aristotle says it is better to posit a smaller finite
number, as Empedocles does.

This records the local comparative preference, not a proof that Empedocles's particular
principles are correct.

Source: Aristotle, *Physics* I.4, 188a13-17 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PreferFewerFinitePrinciplesReading
    (FewerFinitePrinciplesPreferable : Prop) : Prop :=
  FewerFinitePrinciplesPreferable

end TruthCore.Greek.Aristotle.Physics
