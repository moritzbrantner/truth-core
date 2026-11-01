import Mathlib.Data.Bool.Basic
import TruthCore.Causality.CountTemporalNecessity

/-! Source-free joint model of the EXACT guarded temporal-count interface.
The existing Option Bool mixed scenario has only two contingent candidates;
existing four-candidate history controls cannot realize five distinct
contingents. This finite enlargement reuses History/Ontic without replacing
causal or modal meanings. It establishes no metaphysical realizability.
-/
namespace TruthCore.Models.CountTemporalControls
open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.CountTemporalNecessity
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)

abbrev Being := Option (Fin 5)

/-- The source is present always; each of five distinct effects occurs only
at the later time of world true. Ontic presence has the ever-history reading. -/
def history : History Bool Being Bool where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := fun w x => match x with
      | none => True
      | some _ => w = true
    Causes := fun _ _ _ => False }
  IsAt := fun w x t => match x with
    | none => True
    | some _ => w = true ∧ t = true
  now := true

def Concrete (_ : Being) : Prop := True

/-- A fixture marker restricted to realizable positive counts, not an
ordinary individual-to-individual cause or universal causal principle. -/
def CauseCount (w : Bool) (c : Being) (n : Nat) (t : Bool) : Prop :=
  w = true ∧ c = none ∧ t = true ∧ 0 < n ∧ n ≤ 5

/-- All six original inputs hold together, conditional on the explicit logical
EM input. Retain the SAME none cause and a five-fold target, and witness an
actual contingent individual: no collapse of this population is asserted. -/
def PositiveControl : Prop :=
  FiveThresholdPossible history Concrete CauseCount true ∧
  ThresholdDescent history Concrete CauseCount true ∧
  HistoryPresenceActual history ∧ ExcludedMiddle ∧
  Euclidean history.ontic.frame ∧ ActualReflexive history.ontic true ∧
  (Concrete none ∧ history.ontic.ExistsAt true none ∧
    NecessaryAt history.ontic true none ∧ CauseCount true none 5 true) ∧
  AtLeastAt history Concrete true 5 true ∧
  ContingentAt history.ontic true (some (0 : Fin 5))
end TruthCore.Models.CountTemporalControls
