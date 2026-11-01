import TruthCore.Models.CountTemporalControls
namespace TruthCore.Results.Causality.CountTemporalControls
open TruthCore.Models.CountTemporalControls
open TruthCore.Causality.CountTemporalNecessity
open TruthCore.German.Kant.CosmologicalInference

private theorem sourceNecessary : NecessaryAt history.ontic true none := by
  intro _ _
  trivial

private theorem effectContingent (i : Fin 5) :
    ContingentAt history.ontic true (some i) := by
  refine ⟨rfl, false, True.intro, ?_⟩
  intro hFalse
  cases hFalse

private theorem threshold (n : Nat) (hn : n ≤ 5) :
    AtLeastAt history Concrete true n true := by
  let f : Fin n → Being := fun i => some ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    have hval := congrArg (fun x : Fin 5 => x.val) (Option.some.inj hij)
    exact Fin.ext hval
  · intro i
    exact ⟨True.intro, effectContingent _, rfl, rfl⟩

private theorem noEarlier (n : Nat) (hPositive : 0 < n) :
    ∀ t, t < true → ¬ AtLeastAt history Concrete true n t := by
  intro t hBefore ⟨f, _, hAt⟩
  let i : Fin n := ⟨0, hPositive⟩
  obtain ⟨_, hCont, hPresent⟩ := hAt i
  cases hfi : f i with
  | none =>
      rw [hfi] at hCont
      obtain ⟨u, _, hAbsent⟩ := hCont.2
      exact hAbsent True.intro
  | some j =>
      rw [hfi] at hPresent
      have ht : t = true := hPresent.2
      subst t
      exact (lt_irrefl true) hBefore

private theorem caused (n : Nat) (hPositive : 0 < n) (hn : n ≤ 5) :
    CausedThreshold history Concrete CauseCount true n := by
  exact ⟨none, false, true, True.intro, True.intro, by decide,
    ⟨rfl, rfl, rfl, hPositive, hn⟩, threshold n hn, noEarlier n hPositive⟩

private theorem descent : ThresholdDescent history Concrete CauseCount true := by
  intro n hn hPossible
  obtain ⟨v, _, c, _, t0, _, _, _, hCause, _, _⟩ := hPossible
  have hBound : n ≤ 5 := hCause.2.2.2.2
  exact ⟨true, True.intro,
    caused (n - 1) (Nat.sub_pos_of_lt hn) (Nat.le_trans (Nat.sub_le n 1) hBound)⟩

private theorem presence : HistoryPresenceActual history := by
  intro w c t hAt
  cases c with
  | none => trivial
  | some _ => exact hAt.1

/-- Joint positive model of the original six temporal-count inputs, with a
necessary source and five distinct contingent targets. EM stays explicit. -/
theorem checks (hEM : TruthCore.Logic.ExcludedMiddle) : PositiveControl := by
  exact ⟨⟨true, True.intro, caused 5 (by decide) (by decide)⟩,
    descent, presence, hEM, (fun _ _ _ _ _ => True.intro), True.intro,
    ⟨True.intro, True.intro, sourceNecessary, rfl, rfl, rfl, by decide, by decide⟩,
    threshold 5 (by decide), effectContingent 0⟩
end TruthCore.Results.Causality.CountTemporalControls
