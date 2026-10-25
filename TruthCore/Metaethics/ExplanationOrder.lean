import TruthCore.English.VanRoojen.MoralCognitivism
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaSecundae.Question94.Article4
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaSecundae.Question94.Article5
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question48.Articles2and3
import TruthCore.Refutations.QuasiRealism
import TruthCore.Metaethics.Questions

/-!
Typed test of #191. Explanation is a primitive directed relation on distinct
kinds of relata; semantic explanation of truth conditions is NOT the relation
of a fact making an individual judgment true. No law connects these relations
in the pinned SEP passages. `Data` is a deliberately limited fixture interface,
not a theory of all moral facts or an attribution to quasi-realism.

We give the test particularly strong evil data: Aquinas's due-good/privation
readings, with the same beings and due/possessed goods across differing
practices, and the truth of the evil premise in every practice. This is an
adopted test requirement, not an assertion that quasi-realists accept Catholic
truthmaking or that the SEP semantic explanation criterion denies objective
evil. Evil in q.48 includes non-moral evils: `evilPremise` need not be `Moral`.

The resulting countermodels prove only independence in this encoding. They do
not establish philosophical compatibility of complete worldviews or defend a
grounding account. A source-supported bridge from data to explanatory order
remains a separate research obligation.
-/
namespace TruthCore.Metaethics.ExplanationOrder

open TruthCore.English.VanRoojen
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Refutations.QuasiRealism

/-- Distinct explanatory relata, preventing a silent identification of moral
use, semantic truth conditions and competence with supervenience. -/
inductive Topic (Sentence : Type) where
  | use (φ : Sentence)
  | truthConditions (φ : Sentence)
  | purposesOfMoralTalk
  | supervenienceRequirement
  deriving DecidableEq

/-- The non-explanatory interpretation shared literally by both models.
`Practice` indexes differing acceptance patterns, not possible physical worlds;
due goods and their possession are intentionally held fixed in this test. -/
structure Data where
  Practice : Type
  Agent : Type
  Sentence : Type
  Matter : Type
  Being : Type
  Perfection : Type
  Moral : Sentence → Prop
  TruthApt : Sentence → Prop
  Holds : Practice → Sentence → Prop
  Accepts : Practice → Agent → Sentence → Prop
  BelievesGood : Agent → Matter → Prop
  NaturallyEvil : Matter → Prop
  NeedsCorrection : Agent → Matter → Prop
  germans : Agent
  robberyNotUnjust : Sentence
  Due : Being → Perfection → Prop
  Has : Being → Perfection → Prop
  Evil : Being → Prop
  evilPremise : Sentence

/-- The encoded test data: q.94's error and need for correction, q.48's
privation/truth readings in each practice, and genuinely differing acceptance.
No claim that an actual correction has happened is included. The last conjunct
makes the tested attitude independence explicit for the evil premise only. -/
def SharedData (d : Data) : Prop :=
  MoralJudgmentsAreTruthAptReading d.Moral d.TruthApt ∧
  (∀ p, GermansHeldRobberyNotUnjustReading (d.Accepts p) d.Moral (d.Holds p)
    d.germans d.robberyNotUnjust) ∧
  CorruptedNaturalLawNeedsCorrectionReading d.BelievesGood d.NaturallyEvil d.NeedsCorrection ∧
  EvilIsPrivationReading d.Evil d.Due d.Has ∧
  SomethingFallsShortOfDueGoodReading d.Due d.Has ∧
  (∀ p, EvilIsAsPropositionalTruthReading d.Evil (d.Holds p) d.evilPremise) ∧
  (∃ p q x φ, d.Accepts p x φ ∧ ¬ d.Accepts q x φ) ∧
  (∀ p q, d.Holds p d.evilPremise ↔ d.Holds q d.evilPremise)

def Anti (d : Data) (e : Topic d.Sentence → Topic d.Sentence → Prop) : Prop :=
  AntirealistOrderOfExplanationReading d.Moral
    (fun φ => e (.use φ) (.truthConditions φ))

def Realist (d : Data) (e : Topic d.Sentence → Topic d.Sentence → Prop) : Prop :=
  RealistOrderOfExplanationReading d.Moral
    (fun φ => e (.truthConditions φ) (.use φ))

def Asymmetric (d : Data) (e : Topic d.Sentence → Topic d.Sentence → Prop) : Prop :=
  ExplanatoryOrderAsymmetric d.Moral
    (fun φ => e (.use φ) (.truthConditions φ))
    (fun φ => e (.truthConditions φ) (.use φ))

def BlackburnEdge (d : Data) (e : Topic d.Sentence → Topic d.Sentence → Prop) : Prop :=
  SupervenienceExplainedByPurposesReading e .purposesOfMoralTalk .supervenienceRequirement

/-- Encoding independence: one and the same non-explanatory data admits
opposed explanation relations, each with the same competence explanation and
the explicit asymmetry condition. This says nothing about an unencoded
philosophical bridge or the truth of a complete realist/anti-realist theory. -/
def SharedDataDoNotChooseOrder : Prop :=
  ∃ d : Data, SharedData d ∧
    (∀ p, SomeMoralError (d.Accepts p) d.Moral d.TruthApt (d.Holds p)) ∧
    (∀ p, d.Holds p d.evilPremise) ∧
    ∃ a r : Topic d.Sentence → Topic d.Sentence → Prop,
      Anti d a ∧ ¬ Realist d a ∧ Asymmetric d a ∧ BlackburnEdge d a ∧
      Realist d r ∧ ¬ Anti d r ∧ Asymmetric d r ∧ BlackburnEdge d r

end TruthCore.Metaethics.ExplanationOrder
