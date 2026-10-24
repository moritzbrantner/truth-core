import TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryBeing.Solution
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSe
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryBeing

/-- ST I q.2 a.3 co., the whole *tertia via* on the plenitude reading. Something
is necessary (`tertiaViaSomethingNecessary`). Every necessary being has the cause
of its necessity from elsewhere or not (excluded middle); a cause of a necessary
being's necessity is itself necessary; and there is no infinite regress among
necessary beings caused by another. So every necessary being is necessary per se
or has its necessity, through a finite chain, from something necessary per se;
in particular something is necessary per se. -/
theorem tertiaViaNecessaryPerSe {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (Possible : (Time → Prop) → Prop) (CausesNecessityOf : Being → Being → Prop)
    (hEM : ExcludedMiddle)
    (hPlenitude : PlenitudeOverInfinitePastReading Before now Possible)
    (hInfinitePast : PastIsInfinite Before now)
    (hCollective : AllCanNotBeThenNothingPossibleReading Possible IsAt)
    (hBegin : NothingBeginsExceptThroughWhatIsReading IsAt Before)
    (hNow : SomethingNowIsReading IsAt now)
    (hCauseNecessary :
      CauseOfNecessityIsNecessaryReading Possible IsAt CausesNecessityOf)
    (hNoRegress :
      NoInfiniteRegressInCausedNecessariesReading Possible IsAt CausesNecessityOf) :
    NecessaryPerSeBeingReading Possible IsAt CausesNecessityOf := by
  -- INF-AQUINAS-TERTIA-VIA-NECESSARY-PER-SE: ground every necessary being,
  -- by well-founded induction on the series of caused necessaries
  have hGround : ∀ x, IsNecessary Possible IsAt x →
      ∃ n, IsNecessaryPerSe Possible IsAt CausesNecessityOf n ∧
        (n = x ∨ Relation.TransGen
          (NecessityCausedAmongNecessaries Possible IsAt CausesNecessityOf) n x) := by
    intro x
    induction hNoRegress x with
    | intro x _ ih =>
      intro hx
      -- vel habet causam suae necessitatis aliunde, vel non habet
      cases hEM (HasCauseOfNecessityAliunde CausesNecessityOf x) with
      | inr hNo => exact ⟨x, ⟨hx, hNo⟩, Or.inl rfl⟩
      | inl hHas =>
        obtain ⟨c, hcx, hc⟩ := hHas
        have hcN : IsNecessary Possible IsAt c := hCauseNecessary c x hx hc
        have hLink : NecessityCausedAmongNecessaries Possible IsAt CausesNecessityOf c x :=
          ⟨hcN, hx, hcx, hc⟩
        obtain ⟨n, hn, hPath⟩ := ih c hLink hcN
        refine ⟨n, hn, Or.inr ?_⟩
        cases hPath with
        | inl hEq => subst hEq; exact Relation.TransGen.single hLink
        | inr hChain => exact Relation.TransGen.tail hChain hLink
  -- something is necessary (the first part of the tertia via), so something is
  -- necessary per se
  obtain ⟨x, hx⟩ := tertiaViaSomethingNecessary IsAt Before now Possible hEM
    hPlenitude hInfinitePast hCollective hBegin hNow
  obtain ⟨n, hn, _⟩ := hGround x hx
  exact ⟨⟨n, hn⟩, hGround⟩

/-- The no-regress premise is needed. Times are the natural numbers counted
backwards from `now = 0` (a larger number is earlier). Every being always is (so is necessary)
and `n + 1` causes the necessity of `n`: an infinite descending series of caused
necessaries with no being necessary per se, while every other premise holds. -/
theorem withoutNoRegressNoPerSe :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop)
      (CausesNecessityOf : Being → Being → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      PastIsInfinite Before now →
      AllCanNotBeThenNothingPossibleReading Possible IsAt →
      NothingBeginsExceptThroughWhatIsReading IsAt Before →
      SomethingNowIsReading IsAt now →
      CauseOfNecessityIsNecessaryReading Possible IsAt CausesNecessityOf →
      NecessaryPerSeBeingReading Possible IsAt CausesNecessityOf := by
  intro h
  obtain ⟨⟨n, _, hNo⟩, _⟩ := h Nat Nat (fun _ _ => True) (fun a b => b < a) 0
    (fun φ => ∃ t, 0 < t ∧ φ t) (fun c x => c = x + 1)
    (fun _ _ ⟨t, ht, hφ⟩ => ⟨t, ht, hφ⟩)
    (fun t _ => ⟨t + 1, Nat.lt_succ_self t⟩)
    (fun hAll => absurd (hAll 0) (fun ⟨_, _, hNot⟩ => hNot trivial))
    (fun x _ _ _ _ _ => ⟨x, trivial⟩)
    ⟨0, trivial⟩
    (fun _ _ _ _ ⟨_, _, hNot⟩ => hNot trivial)
  exact hNo ⟨n + 1, Nat.succ_ne_self n, rfl⟩

/-- The premise that a cause of necessity is itself necessary is needed. `true`
always is and `false` never is; `false` causes the necessity of `true`. The
regress premise holds (no caused necessary has a necessary cause), every other
premise holds, and nothing is necessary per se. -/
theorem withoutNecessaryCauseNoPerSe :
    ¬ ∀ (Being Time : Type) (IsAt : Being → Time → Prop)
      (Before : Time → Time → Prop) (now : Time) (Possible : (Time → Prop) → Prop)
      (CausesNecessityOf : Being → Being → Prop),
      PlenitudeOverInfinitePastReading Before now Possible →
      PastIsInfinite Before now →
      AllCanNotBeThenNothingPossibleReading Possible IsAt →
      NothingBeginsExceptThroughWhatIsReading IsAt Before →
      SomethingNowIsReading IsAt now →
      NoInfiniteRegressInCausedNecessariesReading Possible IsAt CausesNecessityOf →
      NecessaryPerSeBeingReading Possible IsAt CausesNecessityOf := by
  intro h
  have hFalseContingent :
      PossibleNotToBe (fun φ => ∃ t : Nat, 0 < t ∧ φ t)
        (fun (b : Bool) (_ : Nat) => b = true) false :=
    ⟨1, Nat.zero_lt_one, Bool.noConfusion⟩
  obtain ⟨⟨n, hnN, hNo⟩, _⟩ := h Bool Nat (fun b _ => b = true) (fun a b => b < a) 0
    (fun φ => ∃ t, 0 < t ∧ φ t) (fun c x => c = false ∧ x = true)
    (fun _ _ ⟨t, ht, hφ⟩ => ⟨t, ht, hφ⟩)
    (fun t _ => ⟨t + 1, Nat.lt_succ_self t⟩)
    (fun hAll => absurd (hAll true) (fun ⟨_, _, hNot⟩ => hNot rfl))
    (fun _ _ _ _ hNot hAt => absurd hAt hNot)
    ⟨true, rfl⟩
    (fun x => Acc.intro x (fun c ⟨hcN, _, _, hc⟩ => by
      rw [hc.1] at hcN
      exact absurd hFalseContingent hcN))
  cases n with
  | false => exact hnN hFalseContingent
  | true => exact hNo ⟨false, Bool.noConfusion, rfl, rfl⟩

end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaNecessaryPerSe
