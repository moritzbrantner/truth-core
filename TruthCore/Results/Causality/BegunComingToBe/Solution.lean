module

public import TruthCore.Causality.BegunComingToBe
public import TruthCore.Results.Causality.ContingentComingToBe.Solution
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace TruthCore.Results.Causality.BegunComingToBe
open TruthCore.Causality.BegunComingToBe
open TruthCore.Causality.ContingentComingToBe (PossiblyFoundedComingToBe)
open TruthCore.Causality.InertEmptiness (ContingentsAbsentThenPresentAt
  PossiblyContingentsAbsentThenPresent)
open TruthCore.Modal.TemporalHistory (History)

/-- A founded past has a beginning: the minimal moment below it. -/
theorem begunOfAcc {T : Type} [Preorder T] (t : T)
    (hAcc : Acc (fun a b : T => a < b) t) : BegunAt t :=
  TruthCore.Results.Causality.ContingentComingToBe.minimalBelow t hAcc

/-- Strength order: founded coming-to-be gives begun coming-to-be. -/
theorem possiblyBegunOfFounded {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W)
    (hFounded : PossiblyFoundedComingToBe h Concrete w) :
    PossiblyBegunComingToBe h Concrete w := by
  obtain ⟨v, hwv, hCome, x, t, hx, hCont, hxt, hAcc⟩ := hFounded
  exact ⟨v, hwv, hCome, x, t, hx, hCont, hxt, begunOfAcc t hAcc⟩

/-- In a history of begun coming-to-be, the first moment of the populated
moment's past is free of contingent concrete individuals and strictly earlier:
anything contingent present at a first moment would need a still earlier
moment of absence. -/
theorem absentThenPresentAt {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W)
    (hBegun : BegunComingToBeAt h Concrete v) :
    ContingentsAbsentThenPresentAt h Concrete v := by
  obtain ⟨hCome, x, t, hx, hCont, hxt, m, hm, hMin⟩ := hBegun
  have hmt : m < t := by
    rcases hm with rfl | hm
    · obtain ⟨s, hs, _⟩ := hCome x hx hCont m hxt
      exact absurd hs (hMin s)
    · exact hm
  refine ⟨m, t, hmt, ?_, x, hx, hCont, hxt⟩
  intro y hy hyCont hym
  obtain ⟨r, hr, _⟩ := hCome y hy hyCont m hym
  exact hMin r hr

/-- The possibility of begun coming-to-be gives the possible contingent-free
past (premise A3 of the modal spine). No frame condition, presence contract,
inertness of emptiness or well-foundedness is used. -/
theorem possibleContingentFreePast {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (w : W)
    (hPossible : PossiblyBegunComingToBe h Concrete w) :
    PossiblyContingentsAbsentThenPresent h Concrete w := by
  obtain ⟨v, hwv, hBegun⟩ := hPossible
  exact ⟨v, hwv, absentThenPresentAt h Concrete v hBegun⟩

/-- No integer moment of `WithBot ℤ` has a founded past. -/
theorem coeNotAcc (n : Int) :
    ¬ Acc (fun a b : WithBot Int => a < b) (n : WithBot Int) := by
  intro hAcc
  generalize hk : (n : WithBot Int) = k at hAcc
  induction hAcc generalizing n with
  | intro k _ ih =>
    subst hk
    exact ih ((n - 1 : Int) : WithBot Int) (WithBot.coe_lt_coe.mpr (by omega)) (n - 1) rfl

theorem nnratHalfLt (t : ℚ≥0) (ht : 0 < t) : t / 2 < t := half_lt_self_iff.mpr ht

theorem nnratHalfPos (t : ℚ≥0) (ht : 0 < t) : 0 < t / 2 := by positivity

/-- In continuous time with a beginning (non-negative rationals), no moment
after `0` has a founded past: `t, t/2, t/4, …` descend endlessly. -/
theorem nnratNotAcc (t : ℚ≥0) (ht : 0 < t) :
    ¬ Acc (fun a b : ℚ≥0 => a < b) t := by
  intro hAcc
  revert ht
  induction hAcc with
  | intro t _ ih => intro ht; exact ih (t / 2) (nnratHalfLt t ht) (nnratHalfPos t ht)

/-- In the same order every moment's past has a beginning, `0`. -/
theorem nnratBegun (t : ℚ≥0) : BegunAt t :=
  ⟨0, eq_or_lt_of_le (zero_le : (0 : ℚ≥0) ≤ t),
    fun r => not_lt_of_ge (zero_le : (0 : ℚ≥0) ≤ r)⟩

/-- Strictness and nonvacuity control in a history with a beginning and no
earliest moment after it, and the begun-but-not-founded order of continuous
time with a beginning. -/
theorem controls : Control.Certificate := by
  refine ⟨?_, ?_, fun _ _ _ hp => hp.1, ?_, ?_, ?_, nnratBegun, nnratNotAcc⟩
  · refine ⟨true, trivial, ?_, 0, (0 : Int), trivial,
      ⟨rfl, false, trivial, Bool.false_ne_true⟩, ⟨rfl, le_refl _⟩, ⊥,
      Or.inr (WithBot.bot_lt_coe 0), fun r => not_lt_bot⟩
    intro x _ _ t hxt
    refine ⟨⊥, lt_of_lt_of_le (WithBot.bot_lt_coe x) hxt.2, fun hp => ?_⟩
    exact WithBot.not_coe_le_bot x hp.2
  · rintro ⟨_, _, _, x, t, _, _, hxt, hAcc⟩
    induction t using WithBot.recBotCoe with
    | bot => exact WithBot.not_coe_le_bot x hxt.2
    | coe k => exact coeNotAcc k hAcc
  · intro x t _ hxt
    refine ⟨x - 1, ((x - 1 : Int) : WithBot Int), rfl, ⟨rfl, rfl⟩, ?_, rfl, le_refl _⟩
    exact lt_of_lt_of_le (WithBot.coe_lt_coe.mpr (by omega)) hxt.2
  · rintro v ⟨x, _, _, hNec⟩
    exact Bool.false_ne_true (hNec false trivial)
  · intro hInert
    have hEmpty : TruthCore.Causality.InertEmptiness.ConcreteEmptyAt Control.zeno
        TruthCore.Causality.InertEmptiness.Control.all true ⊥ :=
      fun x _ hx => WithBot.not_coe_le_bot x hx.2
    exact hInert true ⊥ ((0 : Int) : WithBot Int) (WithBot.bot_lt_coe 0) hEmpty 0
      trivial ⟨rfl, le_refl _⟩

end TruthCore.Results.Causality.BegunComingToBe
