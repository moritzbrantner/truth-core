import TruthCore.Causality.CountTemporalNecessity
import TruthCore.Models.CountTemporalControls

/-! Analyst-defined cause-time configuration, not a source attribution. Reuse
History, the exact AtLeastAt predicate and the supplied CauseCount relation.
Only absence of count one at the selected cause time is required; no temporal
order, first threshold or independently sufficient causal contribution is added.
The existential witness remains an OPEN admission commitment. -/
namespace TruthCore.Causality.CountCauseTimeNecessity
open TruthCore.Causality.CountTemporalNecessity
open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Modal (Euclidean)
open TruthCore.Logic (ExcludedMiddle)

/-- A possible concrete cause is present when the count-one situation is absent.
The retained CauseCount marker has its own supplied target time; no ordering or
later threshold assertion is needed for this pointwise consequence. -/
def CauseTimeOpportunity {W B T : Type} (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ ∃ c tc t0,
    Concrete c ∧ h.IsAt v c tc ∧ CauseCount v c 1 t0 ∧
      ¬ AtLeastAt h Concrete v 1 tc

/-- The SAME concrete individual retains its cause-of-count-one role in the
accessible history, is necessary there, and is actual and necessary at w.
No actual-world causal role, grounding, uniqueness or God identity follows. -/
def NecessaryConcreteCauseAt {W B T : Type} (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W) : Prop :=
  ∃ v, h.ontic.frame.access w v ∧ ∃ c, Concrete c ∧
    (∃ t, CauseCount v c 1 t) ∧ NecessaryAt h.ontic v c ∧
    h.ontic.ExistsAt w c ∧ NecessaryAt h.ontic w c

/-- Reuse the EXACT existing finite history, without changing its fields.
All five new inputs hold together with the old positive background and the
same none cause marker. This is not a metaphysical realizability assertion. -/
def PositiveControl : Prop :=
  let h := TruthCore.Models.CountTemporalControls.history
  let C := TruthCore.Models.CountTemporalControls.Concrete
  let R := TruthCore.Models.CountTemporalControls.CauseCount
  TruthCore.Models.CountTemporalControls.PositiveControl ∧
  (CauseTimeOpportunity h C R true ∧ HistoryPresenceActual h ∧ ExcludedMiddle ∧
    Euclidean h.ontic.frame ∧ ActualReflexive h.ontic true) ∧
  NecessaryConcreteCauseAt h C R true ∧ R true none 1 true

end TruthCore.Causality.CountCauseTimeNecessity
