import TruthCore.Modal.TemporalHistory
import TruthCore.Causality.NecessaryBeingSurvey
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Logic.ExcludedMiddle

/-! Source-free temporal interpretation of the survey count interface.
Worlds, beings and times reuse History without changing its Ontic or now.
The guarded causal configurations are OPEN framework assumptions, not new
attributions to A7. CauseCount is a supplied relation to a threshold situation,
not Ontic.Causes, fact explanation, or a source of structural causal laws.
-/
namespace TruthCore.Causality.CountTemporalNecessity
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.TemporalHistory
open TruthCore.Causality.NecessaryBeingSurvey

/-- n distinct concrete contingent bearers present at one supplied time.
Standard Fin and injectivity express the cardinal lower bound. -/
def AtLeastAt {W B T : Type} (h : History W B T) (Concrete : B → Prop)
    (v : W) (n : Nat) (t : T) : Prop :=
  ∃ f : Fin n → B, Function.Injective f ∧
    ∀ i, Concrete (f i) ∧ ContingentAt h.ontic v (f i) ∧ h.IsAt v (f i) t

/-- A cause bearer present before the first supplied n-threshold occurrence.
The same history has no such threshold at ANY earlier time. No temporal
persistence, global order completeness, or world/now coherence is assumed. -/
def CausedThreshold {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop)
    (v : W) (n : Nat) : Prop :=
  ∃ c tc t0, Concrete c ∧ h.IsAt v c tc ∧ tc < t0 ∧
    CauseCount v c n t0 ∧ AtLeastAt h Concrete v n t0 ∧
    ∀ t, t < t0 → ¬ AtLeastAt h Concrete v n t

/-- Possible guarded threshold production; each count can have a different
accessible world and cause. No simultaneous realization is assumed. -/
def PossibleCount {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop)
    (w : W) (n : Nat) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ CausedThreshold h Concrete CauseCount v n

/-- One-way EVER-history interpretation. This is not CoherentAtNow and does
not follow from History's fields; applying it to reality remains open. -/
def HistoryPresenceActual {W B T : Type} (h : History W B T) : Prop :=
  ∀ v c t, h.IsAt v c t → h.ontic.ExistsAt v c

/-- Guarded five-threshold opportunity, a new typed commitment, not the old
source claim over an uninterpreted count predicate. -/
def FiveThresholdPossible {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W) : Prop :=
  PossibleCount h Concrete CauseCount w 5

/-- Guarded decrement transfer. Temporal guards and witness admission are
retained at each count; arithmetic weakening alone does not supply this. -/
def ThresholdDescent {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W) : Prop :=
  CountDescent (PossibleCount h Concrete CauseCount w)
end TruthCore.Causality.CountTemporalNecessity
