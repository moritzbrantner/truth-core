import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaAscent
import TruthCore.Latin.Aquinas.InMetaphysicam.BookII
import TruthCore.Greek.Aristotle.Metaphysics

/-! Two-being Boolean omission controls for the causal-ascent derivation of the
grades-to-maximum step (`QUARTA-VIA-GRADES-MAXIMUM-FROM-CAUSAL-ASCENT`). Respects are
Booleans and every fixture ignores them. In each fixture exactly one of the four nonlogical
premises fails, the other three hold, something is more such than something,
and nothing is maximal in the respect. These are satisfiability fixtures for
the encoded premises, not metaphysical possibilities or source readings. -/
namespace TruthCore.Models.QuartaViaCausalAscent
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.InMetaphysicam
open TruthCore.Greek.Aristotle.Metaphysics (CauseOfQualityInAnotherIsMoreSuchReading)

/-- The relation the regress premise constrains at respect `r`. -/
def DistinctCause (causesIn : Bool → Bool → Bool → Prop) (r c x : Bool) : Prop :=
  c ≠ x ∧ causesIn c x r

/-- Some grade of some respect exists, and nothing is maximal in any respect. -/
def NoMaximum (inAct : Bool → Bool → Prop) (moreIn : Bool → Bool → Bool → Prop) : Prop :=
  (∃ r x y, moreIn r x y) ∧ ∀ r, ¬ ∃ m, IsMaximumIn inAct moreIn r m

theorem regress_of_acc {causesIn : Bool → Bool → Bool → Prop}
    (h : ∀ r b, Acc (DistinctCause causesIn r) b) :
    NoInfiniteRegressOfCausesOfAPerfectionReading causesIn :=
  fun r => ⟨h r⟩

/-! Only `false` has the perfection, yet `true` is more such than `false` and
causes it in `false`: the hotter thing is not hot. -/
namespace WithoutBearer
def inAct (x : Bool) (_ : Bool) : Prop := x = false
def moreIn (_ : Bool) (x y : Bool) : Prop := x = true ∧ y = false
def causesIn (c x : Bool) (_ : Bool) : Prop := c = true ∧ x = false

theorem bearerFails : ¬ MoreSuchHasThePerfectionReading inAct moreIn := by
  dsimp only [MoreSuchHasThePerfectionReading, inAct, moreIn]; decide
theorem cause : CauseOfQualityInAnotherIsMoreSuchReading causesIn moreIn := by
  dsimp only [CauseOfQualityInAnotherIsMoreSuchReading, causesIn, moreIn]; decide
theorem exceeded : ExceededPerfectionIsCausedReading inAct moreIn causesIn := by
  dsimp only [ExceededPerfectionIsCausedReading, inAct, moreIn, causesIn]; decide
theorem regress : NoInfiniteRegressOfCausesOfAPerfectionReading causesIn := by
  refine regress_of_acc fun r b => ?_
  have hT : Acc (DistinctCause causesIn r) true :=
    ⟨_, fun c h => by simp [DistinctCause, causesIn] at h⟩
  have hF : Acc (DistinctCause causesIn r) false :=
    ⟨_, fun c h => by
      obtain ⟨_, rfl, _⟩ := h
      exact hT⟩
  cases b <;> assumption
theorem noMaximum : NoMaximum inAct moreIn := by
  dsimp only [NoMaximum, IsMaximumIn, inAct, moreIn]; decide
end WithoutBearer

/-! Only `true` has the perfection and it exceeds itself; `false`, which lacks
the perfection and is not more such than anything, causes it in `true`. -/
namespace WithoutCause
def inAct (x : Bool) (_ : Bool) : Prop := x = true
def moreIn (_ : Bool) (x y : Bool) : Prop := x = true ∧ y = true
def causesIn (c x : Bool) (_ : Bool) : Prop := c = false ∧ x = true

theorem bearer : MoreSuchHasThePerfectionReading inAct moreIn := by
  dsimp only [MoreSuchHasThePerfectionReading, inAct, moreIn]; decide
theorem causeFails : ¬ CauseOfQualityInAnotherIsMoreSuchReading causesIn moreIn := by
  dsimp only [CauseOfQualityInAnotherIsMoreSuchReading, causesIn, moreIn]; decide
theorem exceeded : ExceededPerfectionIsCausedReading inAct moreIn causesIn := by
  dsimp only [ExceededPerfectionIsCausedReading, inAct, moreIn, causesIn]; decide
theorem regress : NoInfiniteRegressOfCausesOfAPerfectionReading causesIn := by
  refine regress_of_acc fun r b => ?_
  have hF : Acc (DistinctCause causesIn r) false :=
    ⟨_, fun c h => by simp [DistinctCause, causesIn] at h⟩
  have hT : Acc (DistinctCause causesIn r) true :=
    ⟨_, fun c h => by
      obtain ⟨_, rfl, _⟩ := h
      exact hF⟩
  cases b <;> assumption
theorem noMaximum : NoMaximum inAct moreIn := by
  dsimp only [NoMaximum, IsMaximumIn, inAct, moreIn]; decide
end WithoutCause

/-! Both beings have the perfection and each is more such than each; nothing
causes anything. -/
namespace WithoutExceeded
def inAct (_ : Bool) (_ : Bool) : Prop := True
def moreIn (_ : Bool) (_ _ : Bool) : Prop := True
def causesIn (_ _ : Bool) (_ : Bool) : Prop := False

theorem bearer : MoreSuchHasThePerfectionReading inAct moreIn :=
  fun _ _ _ _ => trivial
theorem cause : CauseOfQualityInAnotherIsMoreSuchReading causesIn moreIn :=
  fun _ _ _ _ h => h.elim
theorem exceededFails : ¬ ExceededPerfectionIsCausedReading inAct moreIn causesIn := by
  intro h
  obtain ⟨_, _, hc⟩ := h true true true trivial trivial
  exact hc
theorem regress : NoInfiniteRegressOfCausesOfAPerfectionReading causesIn :=
  regress_of_acc fun _ b => ⟨b, fun _ h => h.2.elim⟩
theorem noMaximum : NoMaximum inAct moreIn := by
  dsimp only [NoMaximum, IsMaximumIn, inAct, moreIn]; decide
end WithoutExceeded

/-! Both beings have the perfection; each is more such than, and causes it in,
the other: a two-cycle of causes of one perfection. -/
namespace WithoutRegress
def inAct (_ : Bool) (_ : Bool) : Prop := True
def moreIn (_ : Bool) (x y : Bool) : Prop := x ≠ y
def causesIn (c x : Bool) (_ : Bool) : Prop := c ≠ x

theorem bearer : MoreSuchHasThePerfectionReading inAct moreIn :=
  fun _ _ _ _ => trivial
theorem cause : CauseOfQualityInAnotherIsMoreSuchReading causesIn moreIn :=
  fun _ _ _ h _ => h
theorem exceeded : ExceededPerfectionIsCausedReading inAct moreIn causesIn := by
  dsimp only [ExceededPerfectionIsCausedReading, inAct, moreIn, causesIn]; decide
theorem regressFails : ¬ NoInfiniteRegressOfCausesOfAPerfectionReading causesIn := by
  intro h
  have hAcc : ∀ b, Acc (fun c x => c ≠ x ∧ causesIn c x true) b → False := by
    intro b hb
    induction hb with
    | intro x _ ih =>
      have hne : (!x) ≠ x := by cases x <;> decide
      exact ih (!x) ⟨hne, hne⟩
  exact hAcc true ((h true).apply true)
theorem noMaximum : NoMaximum inAct moreIn := by
  dsimp only [NoMaximum, IsMaximumIn, inAct, moreIn]; decide
end WithoutRegress

end TruthCore.Models.QuartaViaCausalAscent
