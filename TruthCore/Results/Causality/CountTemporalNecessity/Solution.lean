import TruthCore.Causality.CountTemporalNecessity
import TruthCore.Results.Causality.NecessaryBeingCountDescent.Solution
namespace TruthCore.Results.Causality.CountTemporalNecessity
open TruthCore.Causality.CountTemporalNecessity
open TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)

/-- Non-corpus helper retaining the SAME cause's role at its accessible
history and its concrete guard. Arena/Scenario necessity helpers would add
irrelevant fact or positive-beginning fields; the two tiny pointwise/frame
proof terms below use the unchanged Ontic directly. -/
theorem sameCause {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W)
    (hFive : FiveThresholdPossible h Concrete CauseCount w)
    (hDescent : ThresholdDescent h Concrete CauseCount w)
    (hPresence : HistoryPresenceActual h)
    (hEM : ExcludedMiddle) (hEuclidean : Euclidean h.ontic.frame)
    (hReflexive : ActualReflexive h.ontic w) :
    ∃ v, h.ontic.frame.access w v ∧ ∃ c, Concrete c ∧
      (∃ t, CauseCount v c 1 t) ∧ NecessaryAt h.ontic v c ∧
      h.ontic.ExistsAt w c ∧ NecessaryAt h.ontic w c := by
  have hOne := TruthCore.Results.Causality.NecessaryBeingCountDescent.fiveToOne
    (PossibleCount h Concrete CauseCount w) hFive hDescent
  obtain ⟨v, hwv, c, tc, t0, hc, hAt, hBefore, hCause, _, hNoEarlier⟩ := hOne
  have he := hPresence v c tc hAt
  have hNotCont : ¬ ContingentAt h.ontic v c := by
    intro hCont
    apply hNoEarlier tc hBefore
    refine ⟨fun _ => c, ?_, fun _ => ⟨hc, hCont, hAt⟩⟩
    intro i j _
    exact Fin.ext ((Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)).trans
      (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt)).symm)
  have hn : NecessaryAt h.ontic v c := by
    intro u hvu
    rcases hEM (h.ontic.ExistsAt u c) with hPresent | hAbsent
    · exact hPresent
    · exact (hNotCont ⟨he, u, hvu, hAbsent⟩).elim
  exact ⟨v, hwv, c, hc, ⟨t0, hCause⟩, hn,
    hn w (hEuclidean w v w hwv hReflexive),
    fun z hwz => hn z (hEuclidean w v z hwv hwz)⟩

/-- Six explicit inputs connect guarded five-count opportunity to one actual
necessary individual. No input's philosophical truth is established. -/
theorem necessaryBeing {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (CauseCount : W → B → Nat → T → Prop) (w : W)
    (hFive : FiveThresholdPossible h Concrete CauseCount w)
    (hDescent : ThresholdDescent h Concrete CauseCount w)
    (hPresence : HistoryPresenceActual h)
    (hEM : ExcludedMiddle) (hEuclidean : Euclidean h.ontic.frame)
    (hReflexive : ActualReflexive h.ontic w) : NecessaryBeing h.ontic w := by
  obtain ⟨_, _, c, _, _, _, he, hn⟩ :=
    sameCause h Concrete CauseCount w hFive hDescent hPresence hEM hEuclidean hReflexive
  exact ⟨c, he, hn⟩
end TruthCore.Results.Causality.CountTemporalNecessity
