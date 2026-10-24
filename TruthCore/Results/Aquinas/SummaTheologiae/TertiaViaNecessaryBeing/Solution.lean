import TruthCore.Logic.ExcludedMiddle
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryBeing
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- ST I q.2 a.3 co., the *tertia via* up to *oportet aliquid esse necessarium*,
on the plenitude reading. If everything could not-be, then (collective
possibility) it would be possible that nothing is; with an infinite past, that
possibility has been realized (plenitude), so once nothing was. But what is not
begins only through what is, so nothing would be now; yet something is. So not
everything can not-be, and (excluded middle) something is necessary. -/
theorem tertiaViaSomethingNecessary {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (Possible : (Time → Prop) → Prop)
    (hEM : ExcludedMiddle)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hInfinitePast : PastIsInfinite Before now)
    (hCollective : AllCanNotBeThenNothingPossibleReading Possible IsAt)
    (hBegin : NothingBeginsExceptThroughWhatIsReading IsAt Before)
    (hNow : SomethingNowIsReading IsAt now) :
    SomethingIsNecessaryReading Possible IsAt := by
  -- INF-AQUINAS-TERTIA-VIA-ONCE-NOTHING: the contested step
  have hStep : IfAllCanNotBeThenOnceNothingReading Possible IsAt Before now := by
    intro hAll
    exact hPlenitude hInfinitePast _ (hCollective hAll)
  -- INF-AQUINAS-TERTIA-VIA-SOMETHING-NECESSARY: not everything can not-be
  have hNotAll : ¬ ∀ x, PossibleNotToBe Possible IsAt x := by
    intro hAll
    obtain ⟨t0, hBefore, hNothing⟩ := hStep hAll
    obtain ⟨x, hx⟩ := hNow
    obtain ⟨y, hy⟩ := hBegin x t0 now hBefore (hNothing x) hx
    exact hNothing y hy
  -- so some being cannot not-be
  cases hEM (SomethingIsNecessaryReading Possible IsAt) with
  | inl h => exact h
  | inr hNone =>
    exfalso
    apply hNotAll
    intro x
    cases hEM (PossibleNotToBe Possible IsAt x) with
    | inl h => exact h
    | inr h => exact (hNone ⟨x, h⟩).elim

/-- On the plenitude reading, the distributive reading of *quod possibile est non
esse, quandoque non est* follows: plenitude over an infinite past entails that
each thing that can not-be at some (past) time is not. The plenitude reading is
the stronger of the two sibling readings. -/
theorem plenitudeYieldsDistributive {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (Possible : (Time → Prop) → Prop)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hInfinitePast : PastIsInfinite Before now) :
    WhatCanNotBeSometimeIsNotReading Possible IsAt := by
  intro x hx
  obtain ⟨t, _, ht⟩ := hPlenitude hInfinitePast _ hx
  exact ⟨t, ht⟩

/-- The collective-possibility premise is needed, and the distributive reading
does not license the step (the quantifier-shift objection). Relay model: times
are the natural numbers counted backwards from `now = 0` (a larger number is an
earlier time, so the past is infinite), and being `n` is only at time `n`;
possible means realized at some past time. Plenitude, an infinite past, "nothing
begins except through what is", "something now is" and the distributive reading
all hold, every being can not-be, and nothing is necessary. -/
theorem relayWithoutCollectivePossibility :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      PastIsInfinite Before now →
      NothingBeginsExceptThroughWhatIsReading IsAt Before →
      SomethingNowIsReading IsAt now →
      WhatCanNotBeSometimeIsNotReading Possible IsAt →
      SomethingIsNecessaryReading Possible IsAt := by
  intro h
  obtain ⟨x, hx⟩ := h Nat Nat (fun n t => t = n) (fun a b => b < a) 0
    (fun φ => ∃ t, 0 < t ∧ φ t)
    (fun _ _ ⟨t, ht, hφ⟩ => ⟨t, ht, hφ⟩)
    (fun t _ => ⟨t + 1, Nat.lt_succ_self t⟩)
    (fun _ t0 _ _ _ _ => ⟨t0, rfl⟩)
    ⟨0, rfl⟩
    (fun _ ⟨t, _, ht⟩ => ⟨t, ht⟩)
  exact hx ⟨x + 1, Nat.succ_pos x, Nat.succ_ne_self x⟩

/-- The infinite past is needed. Finite past: a single being that is only at the
first time, `now = 0`. The plenitude premise holds vacuously, collective
possibility, "nothing begins except through what is" and "something now is"
hold, and the being can not-be. -/
theorem finitePastNoNecessaryBeing :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      AllCanNotBeThenNothingPossibleReading Possible IsAt →
      NothingBeginsExceptThroughWhatIsReading IsAt Before →
      SomethingNowIsReading IsAt now →
      SomethingIsNecessaryReading Possible IsAt := by
  intro h
  obtain ⟨x, hx⟩ := h Unit Nat (fun _ t => t = 0) (fun a b => a < b) 0
    (fun φ => ∃ t, φ t)
    (fun hInf _ _ => by
      obtain ⟨t', ht'⟩ := hInf 0 (Or.inl rfl)
      exact absurd ht' (Nat.not_lt_zero t'))
    (fun _ => ⟨1, fun _ h1 => Nat.noConfusion h1⟩)
    (fun _ t0 t hlt _ hAt => by subst hAt; exact absurd hlt (Nat.not_lt_zero t0))
    ⟨(), rfl⟩
  exact hx ⟨1, fun h1 => Nat.noConfusion h1⟩

/-- "Nothing begins except through what is" is needed. Times as in
`relayWithoutCollectivePossibility`; a single being that is only now, after
nothing was: every other premise holds and the being can not-be. -/
theorem withoutNothingFromNothingNoNecessaryBeing :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      PastIsInfinite Before now →
      AllCanNotBeThenNothingPossibleReading Possible IsAt →
      SomethingNowIsReading IsAt now →
      SomethingIsNecessaryReading Possible IsAt := by
  intro h
  obtain ⟨x, hx⟩ := h Unit Nat (fun _ t => t = 0) (fun a b => b < a) 0
    (fun φ => ∃ t, 0 < t ∧ φ t)
    (fun _ _ ⟨t, ht, hφ⟩ => ⟨t, ht, hφ⟩)
    (fun t _ => ⟨t + 1, Nat.lt_succ_self t⟩)
    (fun _ => ⟨1, Nat.succ_pos 0, fun _ hAt => Nat.noConfusion hAt⟩)
    ⟨(), rfl⟩
  exact hx ⟨1, Nat.succ_pos 0, fun h1 => Nat.noConfusion h1⟩

end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryBeing
