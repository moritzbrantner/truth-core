import TruthCore.Causality.UnderivedCommonSource
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article7Cause

/-! Analyst-defined interfaces for #319. The reused q.3 a.7 reading gives a
uniting cause, but does not index its actual presence or identify CausesIn with
Ontic.Causes. Neither interface below is attributed to Aquinas or established
by the connection. Composite retains the existing q.3 parameter, not a newly
defined proper-part predicate. -/
namespace TruthCore.Causality.UnderivedNonComposite
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NamedPotentialCauser
open TruthCore.Causality.UnderivedCommonSource

/-- A distinct cause-in-esse of an actual target exists at this selected world.
This is a disputed actuality interface, not part of the atemporal q.3 type. -/
def UnitingCausesPresent {W B P : Type} (m : Ontic W B)
    (CausesIn : B → B → P → Prop) (esse : P) (w : W) : Prop :=
  ∀ c x, m.ExistsAt w x → c ≠ x → CausesIn c x esse → m.ExistsAt w c

/-- A q.3 cause-in-esse with actual endpoints is an ordinary causal edge here.
It need not exhaust ordinary causes or equal R-support. -/
def UnitingCausesAreActual {W B P : Type} (m : Ontic W B)
    (CausesIn : B → B → P → Prop) (esse : P) (w : W) : Prop :=
  ∀ c x, m.ExistsAt w c → m.ExistsAt w x → c ≠ x →
    CausesIn c x esse → m.Causes w c x

/-- The SAME #636 witness retains named underivedness and selected-world source
uniqueness, and is noncomposite for the supplied q.3 predicate. No God naming,
essence-esse identity, maximality, or general classical attributes follows. -/
def CommonUnderivedNonComposite {W B : Type} (m : Ontic W B)
    (R : W → B → B → Prop) (w : W) (Composite : B → Prop) : Prop :=
  ∃ n, NamedNecessarilyUnderived m R w n ∧
    UniqueActualSourceAt m w n ∧ ¬ Composite n

/-- A necessary composite actual source whose alleged uniting cause is absent.
The actual graph has one node. This interpretation violates presence only. -/
def absentCause : Ontic Unit Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ x => x = false
  Causes := fun _ c x => c = true ∧ x = false

/-- Both beings exist; false is the unique source, with a forward edge to true.
The atemporal alleged uniting cause points backwards, so correspondence fails. -/
def differentCause : Ontic Unit Bool where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ c x => c = false ∧ x = true

def fixtureComposite (x : Bool) : Prop := x = false
def fixtureUniting (c x : Bool) (_ : Unit) : Prop := c = true ∧ x = false

/-- Explicit separate omission interpretations. Each has the SAME necessary
underived unique actual source false, which remains composite. They are logical
controls, not metaphysically possible composites or source attributions. -/
def InterfaceOmissionControls : Prop :=
  (TruthCore.Latin.Aquinas.SummaTheologiae.CompositeHasAUnitingCauseReading
      fixtureComposite fixtureUniting ()) ∧
  (NamedNecessarilyUnderived absentCause absentCause.Causes () false ∧
    UniqueActualSourceAt absentCause () false ∧ fixtureComposite false ∧
    UnitingCausesAreActual absentCause fixtureUniting () () ∧
    ¬ UnitingCausesPresent absentCause fixtureUniting () ()) ∧
  (NamedNecessarilyUnderived differentCause differentCause.Causes () false ∧
    UniqueActualSourceAt differentCause () false ∧ fixtureComposite false ∧
    UnitingCausesPresent differentCause fixtureUniting () () ∧
    ¬ UnitingCausesAreActual differentCause fixtureUniting () ())
end TruthCore.Causality.UnderivedNonComposite
