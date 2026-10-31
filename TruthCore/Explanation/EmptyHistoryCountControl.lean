import TruthCore.Explanation.EmptyHistoryCausalAvailability
import TruthCore.Models.CountTemporalControls

/-! A source-free positive joint compatibility control on the EXACT old count
history. Empty contingent extension is not empty concrete existence. The
negative fact is admitted explicitly; CauseFact is neither Ontic.Causes nor
Arena.explains. No causal adequacy or metaphysical possibility is established. -/
namespace TruthCore.Explanation.EmptyHistoryCountControl
open TruthCore.Models.CountTemporalControls
open TruthCore.Explanation.PSRStrength (Arena Contingent)
open TruthCore.Explanation.EmptyHistoryCausalAvailability
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Modal (Euclidean)

/-- Fact none is the fixed negative fact; some b is the existence fact of the
old individual b. Facts and individuals retain distinct typed roles. -/
abbrev Fact := Option Being

def arena : Arena Bool Being Fact where
  ontic := history.ontic
  holds := fun w f => match f with
    | none => ∀ b, Concrete b → ¬ ContingentAt history.ontic w b
    | some b => history.ontic.ExistsAt w b
  exist := some
  explains := fun _ _ _ => False
  conjunct := fun _ _ => False

/-- A separate stipulated causal marker, solely at the obtaining negative fact
and actual necessary bearer none in world false. No old causal field changes. -/
def causeFact (w : Bool) (c : Being) (f : Fact) : Prop :=
  w = false ∧ c = none ∧ f = none

/-- Five nonlogical inputs; the sixth (EM) is supplied to checks and retained
inside the exact old count PositiveControl. Coverage retains its three parts. -/
def RetainedInputs : Prop :=
  Euclidean arena.ontic.frame ∧ ActualReflexive arena.ontic true ∧
  NegativeFactMeaning arena Concrete none ∧
  AccessibleEmptyCoverage arena Concrete causeFact true ∧
  PossiblyInhabitedConcreteAt arena Concrete true

/-- Same-history count control and full empty-history premise compatibility,
with a contingent negative fact and positive actual causal-availability witness.
Every world still has a concrete necessary bearer: this control does NOT realize
the necessary-being theorem's no-concrete-coverage-world second branch. -/
def Control : Prop :=
  PositiveControl ∧ arena.ontic = history.ontic ∧
  (∀ w b, arena.holds w (arena.exist b) ↔ history.ontic.ExistsAt w b) ∧
  RetainedInputs ∧ Contingent arena false none ∧
  ActualCausedFact arena Concrete causeFact false none ∧
  ContingentAt arena.ontic true (some (0 : Fin 5)) ∧
  (∀ w, ∃ b, Concrete b ∧ arena.ontic.ExistsAt w b) ∧
  (∀ w b c, ¬ arena.ontic.Causes w b c) ∧
  (∀ w f g, ¬ arena.explains w f g)
end TruthCore.Explanation.EmptyHistoryCountControl
