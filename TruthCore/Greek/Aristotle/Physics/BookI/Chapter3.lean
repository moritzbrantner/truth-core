import TruthCore.Greek.Aristotle.Physics.BookI.Chapter2

namespace TruthCore.Greek.Aristotle.Physics

/--
Diagnostic reading of Aristotle, *Physics* I.3, 186a5-16: Melissus is not entitled to infer
from the premise that whatever has come to be has a beginning that what has not come to be
has no beginning.

`ConverseInferenceLicensed` represents the disputed inferential permission rather than
turning Aristotle's criticism into a stronger claim about the truth values of the two
propositions themselves.

Source: Aristotle, *Physics* I.3, 186a5-16 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MelissusConverseInferenceNotLicensedReading
    (ConverseInferenceLicensed : Prop) : Prop :=
  ¬ ConverseInferenceLicensed

/--
Reply to the Eleatic transition in Aristotle, *Physics* I.3, 186a16-19: being one does not
by itself entail being motionless. Aristotle points to unified things that move and asks why
the whole could not likewise move or alter.

Source: Aristotle, *Physics* I.3, 186a16-19 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def UnityDoesNotEntailMotionlessnessReading
    (UnityEntailsMotionlessness : Prop) : Prop :=
  ¬ UnityEntailsMotionlessness

/--
Qualified unity reading of Aristotle, *Physics* I.3, 186a19-23: Being cannot be one in form
in the unrestricted way under attack, though unity in an underlying material may be possible.

The second conjunct records possibility as a source-level proposition; it does not assert
that Aristotle has already established one universal material substrate.

Source: Aristotle, *Physics* I.3, 186a19-23 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def NotOneInFormMayBeOneInMaterialReading
    (OneInForm : Prop)
    (MayBeOneInMaterial : Prop) : Prop :=
  ¬ OneInForm ∧ MayBeOneInMaterial

/--
Semantic criticism of Parmenides in Aristotle, *Physics* I.3, 186a23-32: the argument is
false where it treats being as if it were said in only one sense.

This reuses the many-senses theme of I.2 at the level of Aristotle's explicit criticism of
Parmenides rather than introducing a new theory of predication.

Source: Aristotle, *Physics* I.3, 186a23-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ParmenideanUnivocalBeingRejectedReading
    (BeingUsedUnivocally : Prop) : Prop :=
  ¬ BeingUsedUnivocally

/--
Predication distinction in Aristotle, *Physics* I.3, 186a25-32: an attribute such as
whiteness differs in definition from the subject that has the attribute, even when no
separate thing corresponding to the attribute is posited.

Source: Aristotle, *Physics* I.3, 186a25-32 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributeDiffersInDefinitionFromBearerReading
    (AttributeSameDefinitionAsBearer : Prop)
    (RequiresSeparateExistence : Prop) : Prop :=
  ¬ AttributeSameDefinitionAsBearer ∧ ¬ RequiresSeparateExistence

/--
Qualified not-being reading of Aristotle, *Physics* I.3, 187a1-6: even if absolute
not-being is excluded, something can still be a particular not-being—something that is not
this or that—without being nothing without qualification.

Source: Aristotle, *Physics* I.3, 187a1-6 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ParticularNotBeingPossibleReading
    (AbsoluteNotBeingExists : Prop)
    (ParticularNotBeingPossible : Prop) : Prop :=
  ¬ AbsoluteNotBeingExists → ParticularNotBeingPossible

/--
Definitional plurality reading of Aristotle, *Physics* I.3, 186b12-33: a substance can be
analyzed in definition into constituents that are themselves genuine items in the account;
Aristotle's example is man, animal, and biped.

The formalization records the anti-monist structural point without deciding a later theory of
essence or genus/species identity.

Source: Aristotle, *Physics* I.3, 186b12-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SubstanceAllowsDefinitionalPluralityReading
    (SubstanceHasDefinitionalConstituents : Prop)
    (DefinitionalConstituentsArePlural : Prop) : Prop :=
  SubstanceHasDefinitionalConstituents ∧ DefinitionalConstituentsArePlural

/--
Final anti-monist conclusion of Aristotle, *Physics* I.3, 187a3-10: understanding being as a
particular substance does not prevent there being many beings; therefore Being cannot be one
in the unrestricted Eleatic sense under discussion.

Source: Aristotle, *Physics* I.3, 187a3-10 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def ParticularSubstanceDoesNotExcludeManyBeingsReading
    (BeingAsParticularSubstance : Prop)
    (ManyBeingsPossible : Prop) : Prop :=
  BeingAsParticularSubstance → ManyBeingsPossible

end TruthCore.Greek.Aristotle.Physics
