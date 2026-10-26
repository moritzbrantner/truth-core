import TruthCore.History.ResurrectionVocabulary

namespace TruthCore.Greek.NewTestament.Philippians.Christology

/-- Subjects named in the letter's third-person account, not identified with
case-signature beings or with Aristotelian substances. -/
inductive Subject | christJesus | god deriving DecidableEq

/-- Lexical forms in 2.6-7. `god` and `slave` retain the contrasted genitives;
`form` is not defined as essence, mere appearance, or Aristotelian form. -/
inductive Form | god | slave deriving DecidableEq

/-- Contents attributed by the letter. The harpagmos constructor retains the
negative judgment about being equal with God without deciding whether the
object is acquisition, retention, or exploitation. Emptying is accompanied by
taking slave form and human likeness, not defined as losing deity. Purpose
retains the ἵνα scope in 2.10-11; it does not assert completed universal homage. -/
inductive Content
  | existsInForm (subject : Subject) (form : Form)
  | doesNotRegardEqualityWithGodAsHarpagmos (subject : Subject)
  | emptiesSelfTakingSlaveFormInHumanLikeness (subject : Subject)
  | foundAsHumanHumblesSelfObedientThroughCrossDeath (subject : Subject)
  | highlyExaltsAndGrantsNameAboveEveryName (agent recipient : Subject)
  | purposesEveryKneeInHeavenEarthUnderEarthBowAtJesusNameAndEveryTongueConfessLordJesusChristToGodFatherGlory
  deriving DecidableEq

/-- Local letter-attribution vocabulary. The existing pilot Report index has
no Philippians content; this extension reuses State without changing its
signature. Unlike Gospel speech attribution, these contents are the letter's
assertions about Christ, not sayings placed in Jesus's mouth. -/
structure Letter where
  pilot : TruthCore.History.Resurrection.State
  presents : Content → Bool

/-- Philippians 2.6: lexical minimum; the disputed harpagmos judgment is
retained without deciding an acquisition/exploitation reading or ontological
account of form/equality. See docs/philippians-christology.md. -/
def ReportedFormAndEquality (l : Letter) : Prop :=
  l.presents (.existsInForm .christJesus .god) = true ∧
  l.presents (.doesNotRegardEqualityWithGodAsHarpagmos .christJesus) = true

/-- Philippians 2.7-8: emptying by taking slave form/human likeness and
self-humbling in obedience through death on a cross; textual attribution only. -/
def ReportedHumiliation (l : Letter) : Prop :=
  l.presents (.emptiesSelfTakingSlaveFormInHumanLikeness .christJesus) = true ∧
  l.presents (.foundAsHumanHumblesSelfObedientThroughCrossDeath .christJesus) = true

/-- Philippians 2.9-11: God exalts Christ and grants the name above every
name, with the stated universal homage/confession purpose and Father's glory.
The purpose is not replaced by an assertion that everyone already confesses. -/
def ReportedExaltation (l : Letter) : Prop :=
  l.presents (.highlyExaltsAndGrantsNameAboveEveryName .god .christJesus) = true ∧
  l.presents .purposesEveryKneeInHeavenEarthUnderEarthBowAtJesusNameAndEveryTongueConfessLordJesusChristToGodFatherGlory = true

end TruthCore.Greek.NewTestament.Philippians.Christology
