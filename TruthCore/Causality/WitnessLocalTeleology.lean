module
public import TruthCore.Causality.TeleologyFirstMover
@[expose] public section
namespace TruthCore.Causality.WitnessLocalTeleology
open TruthCore.Latin.Aquinas.SummaTheologiae TruthCore.Case.Catholicism
open TruthCore.Causality.TeleologyFirstMover.Control
open TruthCore.Results.Aquinas.SummaTheologiae.QuintaViaModels

/-- Local restrictions on the SAME observed body/end. The reduction and motion
bridges remain explicit; no identity of directors across bodies is assumed.
All predicates retain the inherited interpretations and open applicability. -/
def LocalExcept (m : Fixture) (x : W) (e : Unit) (i : Nat) : Prop :=
  (i ≠ 0 → ¬ m.cognition x) ∧
  (i ≠ 1 → m.body x ∧ m.regular x e ∧ m.best x e) ∧
  (i ≠ 2 → m.regular x e → ¬ m.chance x e) ∧
  (i ≠ 3 → m.regular x e → m.best x e → m.chance x e ∨ m.tends x e) ∧
  (i ≠ 4 → ¬ m.cognition x → m.tends x e →
    ∃ d, m.cognition d ∧ m.intelligent d ∧ m.directs d x e) ∧
  (i ≠ 5 → ∀ d, m.body x → m.directs d x e →
    ∃ f, m.cognition f ∧ m.intelligent f ∧ (∀ r, ¬ m.moved f r) ∧ m.directs f x e) ∧
  (i ≠ 6 → ∀ d, m.directs d x e → ∃ r, m.moves d x r)

/-- Carrier-independent version of the same seven witness-local constraints. -/
def Bundle {B R E : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body Cog Intel : B → Prop) (Reg Best Chance Tends : B → E → Prop)
    (Dir : B → B → E → Prop) : Prop :=
  ∃ x e, (¬ Cog x) ∧ (Body x ∧ Reg x e ∧ Best x e) ∧
    (Reg x e → ¬ Chance x e) ∧
    (Reg x e → Best x e → Chance x e ∨ Tends x e) ∧
    (¬ Cog x → Tends x e → ∃ d, Cog d ∧ Intel d ∧ Dir d x e) ∧
    (∀ d, Body x → Dir d x e →
      ∃ f, Cog f ∧ Intel f ∧ (∀ r, ¬ Moved f r) ∧ Dir f x e) ∧
    (∀ d, Dir d x e → ∃ r, Moves d x r)

def Universal {B R E : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Body Cog Intel : B → Prop) (Reg Best Chance Tends : B → E → Prop)
    (Dir : B → B → E → Prop) : Prop :=
  NaturalBodiesLackCognitionReading Body Cog ∧
  NaturalBodiesActRegularlyForTheBestReading Body Reg Best ∧
  RegularityIsNotByChanceReading Reg Chance ∧
  RegularBestByChanceOrByIntentionReading Reg Best Chance Tends ∧
  NonCognitiveTendingNeedsKnowingDirectorReading Cog Intel Tends Dir ∧
  NaturalDirectionReducedToIntelligentImmobileDirector Moved Body Cog Intel Dir ∧
  DirectingIsMoving Moves Dir

/-- A second body lacks regular outcomes, while the observed first body retains
all seven local constraints. This changes actual scope, not a propositional flag. -/
def strict : Fixture := { base with regular := fun x _ => x = .b0 }

def Controls : Prop :=
  Bundle base.moved base.moves base.body base.cognition base.intelligent
    base.regular base.best base.chance base.tends base.directs ∧
  Bundle strict.moved strict.moves strict.body strict.cognition strict.intelligent
    strict.regular strict.best strict.chance strict.tends strict.directs ∧
  LocalExcept base .b0 () 7 ∧
  (LocalExcept strict .b0 () 7 ∧
    ¬ Universal strict.moved strict.moves strict.body strict.cognition strict.intelligent
      strict.regular strict.best strict.chance strict.tends strict.directs) ∧
  (LocalExcept (flat true true false true) .b0 () 0 ∧
    ¬ ThereIsAFirstUnmovedMover (flat true true false true).moved (flat true true false true).moves) ∧
  (LocalExcept (flat false false false false) .b0 () 1 ∧
    ¬ ThereIsAFirstUnmovedMover (flat false false false false).moved (flat false false false false).moves) ∧
  (LocalExcept (flat true false true false) .b0 () 2 ∧
    ¬ ThereIsAFirstUnmovedMover (flat true false true false).moved (flat true false true false).moves) ∧
  (LocalExcept (flat true false false false) .b0 () 3 ∧
    ¬ ThereIsAFirstUnmovedMover (flat true false false false).moved (flat true false false false).moves) ∧
  (LocalExcept (flat true false false true) .b0 () 4 ∧
    ¬ ThereIsAFirstUnmovedMover (flat true false false true).moved (flat true false false true).moves) ∧
  (LocalExcept noReduction .b0 () 5 ∧ ¬ ThereIsAFirstUnmovedMover noReduction.moved noReduction.moves) ∧
  (LocalExcept noMoving .b0 () 6 ∧ ¬ ThereIsAFirstUnmovedMover noMoving.moved noMoving.moves)
end TruthCore.Causality.WitnessLocalTeleology
