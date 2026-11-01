import TruthCore.Causality.CountCauseTimeNecessity
import TruthCore.Results.Causality.NecessaryBeingCountDescent.Solution
import TruthCore.Results.Causality.CountTemporalControls.Solution

namespace TruthCore.Results.Causality.CountCauseTimeNecessity
open TruthCore.Causality.CountCauseTimeNecessity
open TruthCore.Causality.CountTemporalNecessity
open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Modal (Euclidean)
open TruthCore.Logic (ExcludedMiddle)

/-- Five explicit inputs preserve one actual necessary concrete cause witness.
The cause-time opportunity is a packaged OPEN commitment, not a PSR discharge. -/
theorem sameCause {W B T : Type} (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W)
    (hOpportunity : CauseTimeOpportunity h Concrete CauseCount w)
    (hPresence : HistoryPresenceActual h) (hEM : ExcludedMiddle)
    (hEuclidean : Euclidean h.ontic.frame) (hReflexive : ActualReflexive h.ontic w) :
    NecessaryConcreteCauseAt h Concrete CauseCount w := by
  obtain ⟨v, hwv, c, tc, t0, hc, hAt, hCause, hAbsent⟩ := hOpportunity
  have he := hPresence v c tc hAt
  have hNotCont : ¬ ContingentAt h.ontic v c := by
    intro hCont
    apply hAbsent
    refine ⟨fun _ => c, ?_, fun _ => ⟨hc, hCont, hAt⟩⟩
    intro i j _
    exact Fin.ext ((Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)).trans
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)).symm)
  have hn : NecessaryAt h.ontic v c := by
    intro u hvu
    rcases hEM (h.ontic.ExistsAt u c) with hPresent | hMissing
    · exact hPresent
    · exact (hNotCont ⟨he, u, hvu, hMissing⟩).elim
  exact ⟨v, hwv, c, hc, ⟨t0, hCause⟩, hn,
    hn w (hEuclidean w v w hwv hReflexive),
    fun z hwz => hn z (hEuclidean w v z hwv hwz)⟩

/-- Import the existing five-to-one inference, then weaken its witness guards
at the SAME c, tc and t0. No monotonicity of CountDescent is asserted. -/
theorem opportunityOfOld {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W)
    (hFive : FiveThresholdPossible h Concrete CauseCount w)
    (hDescent : ThresholdDescent h Concrete CauseCount w) :
    CauseTimeOpportunity h Concrete CauseCount w := by
  have hOne := TruthCore.Results.Causality.NecessaryBeingCountDescent.fiveToOne
    (PossibleCount h Concrete CauseCount w) hFive hDescent
  obtain ⟨v, hwv, c, tc, t0, hc, hAt, hBefore, hCause, _, hNoEarlier⟩ := hOne
  exact ⟨v, hwv, c, tc, t0, hc, hAt, hCause, hNoEarlier tc hBefore⟩

/-- Entire old six-input bundle implies the entire new five-input bundle.
Two count assumptions are packaged into one opportunity; the other four
commitments are retained verbatim. This is not premise truth or minimality. -/
theorem oldInputsToNewInputs {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W)
    (hFive : FiveThresholdPossible h Concrete CauseCount w)
    (hDescent : ThresholdDescent h Concrete CauseCount w)
    (hPresence : HistoryPresenceActual h) (hEM : ExcludedMiddle)
    (hEuclidean : Euclidean h.ontic.frame) (hReflexive : ActualReflexive h.ontic w) :
    CauseTimeOpportunity h Concrete CauseCount w ∧ HistoryPresenceActual h ∧
      ExcludedMiddle ∧ Euclidean h.ontic.frame ∧ ActualReflexive h.ontic w := by
  exact ⟨opportunityOfOld h Concrete CauseCount w hFive hDescent,
    hPresence, hEM, hEuclidean, hReflexive⟩

/-- Structural projection into the pre-existing shared necessary-being endpoint;
it forgets concreteness, cause role and necessity at the accessible history. -/
theorem necessaryBeingOfWitness {W B T : Type} (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W)
    (hWitness : NecessaryConcreteCauseAt h Concrete CauseCount w) :
    NecessaryBeing h.ontic w := by
  obtain ⟨_, _, c, _, _, _, he, hn⟩ := hWitness
  exact ⟨c, he, hn⟩

/-- The unchanged old finite history jointly realizes the new inputs and
retains five contingent targets and its SAME necessary none cause. -/
theorem checks (hEM : ExcludedMiddle) : PositiveControl := by
  have old := TruthCore.Results.Causality.CountTemporalControls.checks hEM
  have inputs := oldInputsToNewInputs
    TruthCore.Models.CountTemporalControls.history
    TruthCore.Models.CountTemporalControls.Concrete
    TruthCore.Models.CountTemporalControls.CauseCount true
    old.1 old.2.1 old.2.2.1 old.2.2.2.1 old.2.2.2.2.1 old.2.2.2.2.2.1
  refine ⟨old, inputs, ?_, ?_⟩
  · exact sameCause _ _ _ _ inputs.1 inputs.2.1 inputs.2.2.1
      inputs.2.2.2.1 inputs.2.2.2.2
  · exact ⟨rfl, rfl, rfl, by decide, by decide⟩

end TruthCore.Results.Causality.CountCauseTimeNecessity
