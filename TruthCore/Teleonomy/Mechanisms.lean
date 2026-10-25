import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaEachDirected.Solution
import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaActsForAnEnd.Solution

/-!
Mechanism/scope tests for #251. These are deliberately finite countermodels,
not a simulation of Darwinian populations or Dye's continuum equations.
The source claims retain likelihood, experimental context and limitations;
no deterministic toy theorem is attributed to those authors.

Reuse the Fifth Way's Being/End predicates and #179's finite models. Biological
selected function is a historical reproductive effect; `TendsTo` retains the
broader ordering-to-an-end sense of Aquinas, not conscious intention.
-/
namespace TruthCore.Teleonomy
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

/-- A finite selection filter: variants are present before selection; only
heritable, locally advantageous variants persist in this idealized generation.
This is a stipulated special case, not Darwin's probabilistic general law. -/
structure Selection where
  present : Bool → Bool
  heritable : Bool → Bool
  advantageous : Bool → Bool

def retained (s : Selection) (v : Bool) : Bool :=
  s.present v && s.heritable v && s.advantageous v

/-- Nonempty differential retention, with the retained variant inherited and
advantageous in the specified environment. It says nothing about cosmic good. -/
def SelectionCoverage (s : Selection) : Prop :=
  retained s true = true ∧ retained s false = false ∧
  s.heritable true = true ∧ s.advantageous true = true

/-- A particular model of differential retention; no agent occurs in its rule. -/
def selectionExample : Selection := ⟨fun _ => true, fun _ => true, fun v => v⟩

/-- One cell copies its neighbor; the neighbor persists. Local coupling suffices
for a stable aligned pattern in this two-cell toy. It is neither the Dye model
nor an explanation of every instance of nonliving order. -/
def couple (state : Bool × Bool) : Bool × Bool := (state.1, state.1)

def FeedbackCoverage : Prop :=
  couple (true, false) = (true, true) ∧
  ∀ state, couple (couple state) = couple state

/-- Existing teleonomy model: regular, beneficial attainment with broad
immanent tending, without any knower. Only the Fifth Way fragment is encoded;
this does not prove that selection explains every natural thing. -/
def UnguidedFinalityModel : Prop :=
  NaturalBodiesLackCognitionReading isBody noneP ∧
  NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
  RegularityIsNotByChanceReading bodyEnd noEnd ∧
  RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
  ¬ NonCognitiveTendingNeedsKnowingDirectorReading noneP noneP bodyEnd noDirects ∧
  ¬ EachNaturalBodyDirectedByAKnowerReading isBody noneP noneP allEnd noDirects

/-- Mechanisms do not exclude an intelligent director: the same retention and
coupling functions coexist with broad tending and #179's one-director model.
Compatibility here is logical; historical Thomistic acceptance is not claimed. -/
def GovernedMechanismsModel : Prop :=
  SelectionCoverage selectionExample ∧ FeedbackCoverage ∧
  NaturalBodiesActForAnEndNotByChanceReading isBody allEnd noEnd bodyEnd ∧
  OneIntelligentDirectsAllNaturalThingsReading isBody isDirector oneDirects

/-- The #179 two-archer countermodel to the quantifier exchange, retained whole. -/
def LocalToUniversalFails : Prop :=
  NaturalBodiesLackCognitionReading isBody isDirector ∧
  NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
  RegularityIsNotByChanceReading bodyEnd noEnd ∧
  RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd bodyEnd ∧
  NonCognitiveTendingNeedsKnowingDirectorReading isDirector isDirector bodyEnd twoDirects ∧
  EachNaturalBodyDirectedByAKnowerReading isBody isDirector isDirector allEnd twoDirects ∧
  ¬ OneIntelligentDirectsAllNaturalThingsReading isBody isDirector twoDirects

/-- Selection over two organism variants cannot entail an assertion about a
separate nonliving process: keep its observations/Best predicates fixed but
assign the unconnected process different tending predicates. -/
def BiologicalToNonlivingFails : Prop :=
  SelectionCoverage selectionExample ∧
  NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
  ¬ NaturalBodiesActForAnEndNotByChanceReading isBody allEnd noEnd noEnd

/-- Regular beneficial recurrence is consistent with neither accident nor broad
finality, if the dichotomy premise is withheld. This reuses #179's model. -/
def DichotomyFails : Prop :=
  NaturalBodiesLackCognitionReading isBody noneP ∧
  NaturalBodiesActRegularlyForTheBestReading isBody bodyEnd allEnd ∧
  RegularityIsNotByChanceReading bodyEnd noEnd ∧
  ¬ RegularBestByChanceOrByIntentionReading bodyEnd allEnd noEnd noEnd ∧
  ¬ NaturalBodiesActForAnEndNotByChanceReading isBody allEnd noEnd noEnd
end TruthCore.Teleonomy
