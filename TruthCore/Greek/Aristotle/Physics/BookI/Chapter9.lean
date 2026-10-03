import TruthCore.Greek.Aristotle.Physics.BookI.Chapter8

namespace TruthCore.Greek.Aristotle.Physics

/--
Attributed criticism in Aristotle, *Physics* I.9, 191b35-192a13: some predecessors
recognized an underlying nature only inadequately. They accepted unqualified generation
from non-being, treated numerical unity as if it entailed unity in potentiality, and
overlooked a distinct nature required by Aristotle's account.

The declaration records Aristotle's criticism without identifying the unnamed targets or
endorsing their principles.

Source: Aristotle, *Physics* I.9, 191b35-192a13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def RivalMatterAccountInadequateReading
    (AcceptsUnqualifiedGenerationFromNotBeing
      TreatsNumericalUnityAsSinglePotentiality
      OverlooksDistinctNature : Prop) : Prop :=
  AcceptsUnqualifiedGenerationFromNotBeing ∧
    TreatsNumericalUnityAsSinglePotentiality ∧
      OverlooksDistinctNature

/--
Matter/privation distinction in Aristotle, *Physics* I.9, 192a3-13: matter is non-being
incidentally and is near to, or in a qualified sense, substance; privation is non-being in
itself and is in no sense substance.

The qualified language around matter's relation to substance is preserved rather than
strengthened into an unrestricted identification.

Source: Aristotle, *Physics* I.9, 192a3-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterPrivationOntologicalDifferenceReading
    (MatterIsNotBeingIncidentally PrivationIsNotBeingInItself
      MatterIsNearSubstance MatterIsSubstanceInQualifiedSense
      PrivationIsSubstance : Prop) : Prop :=
  MatterIsNotBeingIncidentally ∧
    PrivationIsNotBeingInItself ∧
      MatterIsNearSubstance ∧
        MatterIsSubstanceInQualifiedSense ∧
          ¬ PrivationIsSubstance

/--
Causal role in Aristotle, *Physics* I.9, 192a13-16: the matter which persists is, together
with form, a joint cause of things that come to be.

The source's maternal analogy is not converted into a general biological claim.

Source: Aristotle, *Physics* I.9, 192a13-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PersistentMatterJointCauseWithFormReading
    (MatterPersists MatterAndFormAreJointCauses : Prop) : Prop :=
  MatterPersists ∧ MatterAndFormAreJointCauses

/--
Desiderative distinction in Aristotle, *Physics* I.9, 192a16-25: matter desires form, while
form does not desire itself and the contrary does not desire form because contraries destroy
one another.

`Desires` remains an uninterpreted source-relative predicate. The passage's gendered and
aesthetic analogies are therefore neither generalized nor treated as literal accounts of
matter.

Source: Aristotle, *Physics* I.9, 192a16-25 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterDesiresFormNotSelfOrContraryReading
    (MatterNaturallyDesiresForm FormDesiresItself ContraryDesiresForm : Prop) : Prop :=
  MatterNaturallyDesiresForm ∧ ¬ FormDesiresItself ∧ ¬ ContraryDesiresForm

/--
Qualified generation and perishing in Aristotle, *Physics* I.9, 192a25-34: matter may be
said to come to be or perish in one respect, especially as bearing privation, but not in its
own nature qua potentiality.

This records the chapter's qualification without asserting that every material constituent
of every generated thing is everlasting.

Source: Aristotle, *Physics* I.9, 192a25-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def QualifiedMatterGenerationAndPerishingReading
    (MatterComesToBeOrPerishesAsBearingPrivation
      MatterComesToBeOrPerishesQuaPotentiality : Prop) : Prop :=
  MatterComesToBeOrPerishesAsBearingPrivation ∧
    ¬ MatterComesToBeOrPerishesQuaPotentiality

/--
Definition in Aristotle, *Physics* I.9, 192a25-34: matter is the primary substratum of each
thing, from which that thing comes to be without qualification and which persists in it,
not incidentally.

The predicates are left primitive so that the definition does not silently introduce a
later theory of prime matter or numerical identity through change.

Source: Aristotle, *Physics* I.9, 192a25-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterPrimarySubstratumDefinitionReading
    (MatterIsPrimarySubstratum
      ThingComesFromMatterNonIncidentally
      MatterPersistsInThing : Prop) : Prop :=
  MatterIsPrimarySubstratum ∧
    ThingComesFromMatterNonIncidentally ∧
      MatterPersistsInThing

/--
Reductio premises in Aristotle, *Physics* I.9, 192a25-34: if matter came to be, it would
already exist before coming to be as the required substratum; if it perished, it would
already have perished before perishing as the terminal substratum.

Source: Aristotle, *Physics* I.9, 192a25-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterGenerationPerishingReductiosReading
    (MatterComesToBe MatterExistsBeforeComingToBe
      MatterPerishes MatterAlreadyPerishedBeforePerishing : Prop) : Prop :=
  (MatterComesToBe → MatterExistsBeforeComingToBe) ∧
    (MatterPerishes → MatterAlreadyPerishedBeforePerishing)

/--
Contradictory outcomes excluded in Aristotle's *Physics* I.9, 192a25-34 argument: matter
cannot already exist before its own coming to be or already have perished before its own
perishing.

Source: Aristotle, *Physics* I.9, 192a25-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterReductioOutcomesImpossibleReading
    (MatterExistsBeforeComingToBe MatterAlreadyPerishedBeforePerishing : Prop) : Prop :=
  ¬ MatterExistsBeforeComingToBe ∧ ¬ MatterAlreadyPerishedBeforePerishing

/--
Conclusion of Aristotle's *Physics* I.9, 192a25-34 argument: in its own nature qua
potentiality, matter is necessarily ungenerated and imperishable.

The qualification is essential; it coexists with the chapter's claim that matter may be
described as generated or perishing in another respect.

Source: Aristotle, *Physics* I.9, 192a25-34 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MatterUngeneratedImperishableQuaPotentialityReading
    (MatterComesToBe MatterPerishes : Prop) : Prop :=
  ¬ MatterComesToBe ∧ ¬ MatterPerishes

/--
Division of inquiry in Aristotle, *Physics* I.9, 192a34-192b2: exact determination of the
formal principle belongs to first philosophy, while natural and perishable forms will be
treated in the subsequent physical inquiry.

Source: Aristotle, *Physics* I.9, 192a34-192b2 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def FormalPrincipleInquiryDeferredReading
    (ExactFormalPrincipleBelongsToFirstPhilosophy
      NaturalPerishableFormsTreatedLaterInPhysics : Prop) : Prop :=
  ExactFormalPrincipleBelongsToFirstPhilosophy ∧
    NaturalPerishableFormsTreatedLaterInPhysics

end TruthCore.Greek.Aristotle.Physics
