module
public import TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaOneGovernor.Solution

/-! Analyst target/scope audit, attribution deferred. All philosophical predicates
and seven premises are the existing Fifth Way readings, not fresh definitions.
The finite fixture below is only a control interpretation. First-mover existence
is not uniqueness, classical attributes, Christianity or Catholicism. -/
@[expose] public section
namespace TruthCore.Causality.TeleologyFirstMover
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Case.Catholicism
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

namespace Control
/-- The existing four-being/one-end/one-respect control carrier and vocabulary. -/
structure Fixture where
  moved : W → Unit → Prop
  moves : W → W → Unit → Prop
  body : W → Prop
  cognition : W → Prop
  intelligent : W → Prop
  regular : W → Unit → Prop
  best : W → Unit → Prop
  chance : W → Unit → Prop
  tends : W → Unit → Prop
  directs : W → W → Unit → Prop

/-- i=7 retains all seven premises; i=0..6 omits exactly that hypothesis. -/
def AllExcept (m : Fixture) (i : Nat) : Prop :=
  (i ≠ 0 → (NaturalBodiesLackCognitionReading m.body m.cognition)) ∧ (i ≠ 1 → (NaturalBodiesActRegularlyForTheBestReading m.body m.regular m.best)) ∧
  (i ≠ 2 → (RegularityIsNotByChanceReading m.regular m.chance)) ∧ (i ≠ 3 → (RegularBestByChanceOrByIntentionReading m.regular m.best m.chance m.tends)) ∧
  (i ≠ 4 → (NonCognitiveTendingNeedsKnowingDirectorReading m.cognition m.intelligent m.tends m.directs)) ∧ (i ≠ 5 → (NaturalDirectionReducedToIntelligentImmobileDirector m.moved m.body m.cognition m.intelligent m.directs)) ∧ (i ≠ 6 → (DirectingIsMoving m.moves m.directs))

def Omits (m : Fixture) (i : Nat) : Prop :=
  AllExcept m i ∧ ¬ ThereIsAFirstUnmovedMover m.moved m.moves

/-- Five no-director interpretations for the first five omissions. Truth values
vary extensions of the existing predicates, not the logical consequence. -/
def flat (body cognitive chance tends : Bool) : Fixture where
  moved := nothingMoved
  moves := noMoves
  body := fun _ => body = true
  cognition := fun _ => cognitive = true
  intelligent := noneP
  regular := fun _ _ => body = true
  best := allEnd
  chance := fun _ _ => chance = true
  tends := fun _ _ => tends = true
  directs := noDirects

def base : Fixture :=
  ⟨nothingMoved, oneDirects, isBody, isDirector, isDirector,
    bodyEnd, allEnd, noEnd, bodyEnd, oneDirects⟩

def noReduction : Fixture :=
  ⟨directorsMoved, twoDirects, isBody, isDirector, isDirector,
    bodyEnd, allEnd, noEnd, bodyEnd, twoDirects⟩

def noMoving : Fixture := { base with moves := noMoves }

/-- Nonvacuity, every carrying-premise omission, and the two-director survivor
which rejects global uniqueness but still has first movers. No empirical claim. -/
def Controls : Prop :=
  AllExcept base 7 ∧
  ThereIsAFirstUnmovedMover base.moved base.moves ∧
  Omits (flat true true false true) 0 ∧
  Omits (flat false false false false) 1 ∧
  Omits (flat true false true false) 2 ∧
  Omits (flat true false false false) 3 ∧
  Omits (flat true false false true) 4 ∧
  Omits noReduction 5 ∧ Omits noMoving 6 ∧
  (ThereIsAFirstUnmovedMover nothingMoved twoDirects ∧
    ¬ AtMostOneFirstUnmovedMover nothingMoved twoDirects)
end Control
end TruthCore.Causality.TeleologyFirstMover
