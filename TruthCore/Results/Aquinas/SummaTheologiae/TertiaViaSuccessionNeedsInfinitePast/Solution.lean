import TruthCore.Logic.ExcludedMiddle
import TruthCore.Refutations.TertiaVia
namespace TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaSuccessionNeedsInfinitePast
open TruthCore.Logic
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Refutations.TertiaVia

/-- The rival to collective possibility needs an eternal world. Let `t` be now or
earlier. Something is at `t`: something is now, and if it was not already at
`t`, it began through something that was at `t` (the *tertia via*'s own
principle). By the rival's succession, something was before `t`. So no time up
to now is first: the past is infinite. -/
theorem successionNeedsInfinitePast {Being Time : Type}
    (IsAt : Being → Time → Prop) (Before : Time → Time → Prop) (now : Time)
    (hEM : ExcludedMiddle)
    (hBegin : NothingBeginsExceptThroughWhatIsReading IsAt Before)
    (hNow : SomethingNowIsReading IsAt now) :
    SuccessionRequiresInfinitePast IsAt Before now := by
  intro hSuccession t hUpToNow
  obtain ⟨x, hx⟩ := hNow
  -- INF-AQUINAS-SOMETHING-AT-EVERY-TIME-UP-TO-NOW
  have hSomething : ∃ y, IsAt y t := by
    rcases hUpToNow with hNowTime | hBefore
    · exact ⟨x, hNowTime ▸ hx⟩
    · cases hEM (IsAt x t) with
      | inl h => exact ⟨x, h⟩
      | inr h => exact hBegin x t now hBefore h hx
  obtain ⟨y, hy⟩ := hSomething
  -- INF-AQUINAS-SUCCESSION-GIVES-EARLIER-TIME
  obtain ⟨t', hEarlier, _⟩ := hSuccession y t hy
  exact ⟨t', hEarlier⟩

/-- The rival's succession is what makes the past infinite: two times, the
earlier first, and one being at both. Something is now and nothing begins
without what is, but the succession fails and the past is finite. -/
theorem withoutSuccessionFinitePast :
    ∃ (IsAt : Unit → Bool → Prop) (Before : Bool → Bool → Prop),
      NothingBeginsExceptThroughWhatIsReading IsAt Before ∧
      SomethingNowIsReading IsAt true ∧
      ¬ BeingsSucceedWithoutBeginning IsAt Before ∧
      ¬ PastIsInfinite Before true :=
  ⟨fun _ _ => True, fun t t' => t = false ∧ t' = true,
    fun _ _ _ _ _ _ => ⟨(), trivial⟩, ⟨(), trivial⟩,
    fun h => by
      obtain ⟨t', ⟨_, h1⟩, _⟩ := h () false trivial
      exact Bool.noConfusion h1,
    fun h => by
      obtain ⟨t', _, h1⟩ := h false (Or.inr ⟨rfl, rfl⟩)
      exact Bool.noConfusion h1⟩

end TruthCore.Results.Aquinas.SummaTheologiae.TertiaViaSuccessionNeedsInfinitePast
