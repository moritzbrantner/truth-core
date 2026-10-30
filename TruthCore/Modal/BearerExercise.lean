import TruthCore.Results.Case.Catholicism.StageOne.NecessaryIndividual.CausalPowers.Solution
import TruthCore.Modal.NecessaryVariableEffects

/-! #463: task-local comparisons, not a source attribution or an analysis of
intrinsic powers. Reuses #456's exact response table and certified contract.
World labels are alternatives, not times. See docs/bearer-capacity-exercise.md. -/
namespace TruthCore.Modal.BearerExercise
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.NecessaryContingentActivity
open TruthCore.Modal.NecessaryVariableEffects
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Isabelle.AFP.GoedelGod (Box)

/-- Adapter: an activated positive response counts as the modeled outgoing
causal event. No additional event ontology or process identity is asserted. -/
def responseOntic : Ontic Bool Bool where
  frame := alternatingFrame
  ExistsAt := fun w x => CausalPowers.existsAt x w
  Causes := fun w x y => CausalPowers.response x y w true = true

/-- Minimal directed-power marker: the necessary bearer is directed toward a
rigid recipient candidate even when that recipient does not exist. This is
independent stipulated data, not a complete intrinsic-power analysis. -/
def directed (_ : Bool) (x y : Bool) : Prop := x = false ∧ y = true

/-- Exact positive bridge being tested: each local possession yields some
outgoing actual causal edge. No particular recipient is fixed. -/
def ManifestationRule (m : Ontic W E) (power : E → W → Prop) : Prop :=
  ∀ x v, power x v → ExercisesCausation m v x

/-- A necessary capacity yields necessary exercise under the explicit local
manifestation rule. Necessary existence is unnecessary for this inference. -/
theorem necessaryExercise (m : Ontic W E) (power : E → W → Prop)
    (w : W) (x : E) (rule : ManifestationRule m power)
    (capacity : Box m.frame (power x) w) :
    NecessarilyCausesSomething m w x :=
  fun v hv => rule x v (capacity v hv)

/-- Checked omissions plus a noncollapse control. #456 is consumed rather
than reproved. The first implication fails using the same existence extension
and zero response; the second and third use its activated-response adapter.
The directed marker is present in both worlds but does not force exercise.
The final control reuses #462's necessarily active source and contingent effect. -/
def Comparison : Prop :=
  CausalPowers.Compatibility ∧
  SoundDistinctCauses responseOntic ∧
  NecessaryAt responseOntic false false ∧
  (∀ v, directed v false true) ∧
  (¬ (Box alternatingFrame (CausalPowers.existsAt false) false →
    Box alternatingFrame
      (CausalPowers.Capacity alternatingFrame CausalPowers.existsAt
        (fun _ _ _ _ => false) false) false)) ∧
  (¬ (Box alternatingFrame
      (CausalPowers.Capacity alternatingFrame CausalPowers.existsAt
        CausalPowers.response false) false →
    NecessarilyCausesSomething responseOntic false false)) ∧
  ExercisesCausation responseOntic true false ∧
  ¬ ExercisesCausation responseOntic false false ∧
  (¬ (ExercisesCausation responseOntic true false →
    NecessarilyCausesSomething responseOntic true false)) ∧
  (SoundDistinctCauses alternatingEffects ∧
    NecessaryAt alternatingEffects false source ∧
    NecessarilyCausesSomething alternatingEffects false source ∧
    ¬ SameNecessaryEffect alternatingEffects false source ∧
    ContingentAt alternatingEffects false firstEffect ∧
    ¬ Box alternatingEffects.frame (fun v => v = false) false) ∧
  (∀ (W E : Type) (m : Ontic W E) (power : E → W → Prop) (w : W) (x : E),
    ManifestationRule m power → Box m.frame (power x) w →
      NecessarilyCausesSomething m w x)

end TruthCore.Modal.BearerExercise
