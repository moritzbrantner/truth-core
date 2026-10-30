import TruthCore.Causality.TemporalPrimaVia
import TruthCore.Results.Causality.TemporalPrimaVia.Route.Solution
namespace TruthCore.Results.Causality.TemporalPrimaVia.Controls
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Causality.TemporalActualization
open TruthCore.Causality.TemporalPrimaVia
open TruthCore.Case.Catholicism

theorem conflict : StrictPureActConflict := by
  intro E B R T _ clock bearer C Moved Potency Moves Link strict bridge perSe pure t y x r ne mv s pot
  have noLink := Route.no_link_of_strict clock bearer C Link strict bridge
  have first : IsFirstUnmovedMover (Moved t) (Moves t) y :=
    ⟨⟨x, r, mv⟩, fun r' moved => noLink t y x (perSe t y x r ne mv ⟨r', moved⟩)⟩
  exact pure t y first s pot

theorem feedback :
    LocalRoutePremises fbClock feedbackBearer fbRespect feedbackC fbMoves fbMoved fbActual
      fbPotency (fun _ _ _ => False) ∧
    StrictForward fbClock feedbackC ∧
    IsFirstUnmovedMover (fbMoved 1) (fbMoves 1) false ∧
    IsFirstUnmovedMover (fbMoved 2) (fbMoves 2) true ∧
    (¬ ∃ f, (∃ t x r, fbMoves t f x r) ∧ ∀ t r, ¬ fbMoved t f r) ∧
    ¬ FirstUnmovedMoverIsPureAct (fbMoved 1) (fbMoves 1) (PureAct (fbPotency 1)) := by
  have strict : StrictForward fbClock feedbackC := by
    intro e f edge
    simp only [fbClock, feedbackC] at *
    omega
  have first1 : IsFirstUnmovedMover (fbMoved 1) (fbMoves 1) false :=
    ⟨⟨true, false, by simp [fbMoves]⟩, by simp [fbMoved]⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, strict, first1,
    ⟨⟨false, true, by simp [fbMoves]⟩, by simp [fbMoved]⟩, ?_, ?_⟩
  · intro e f edge rev
    exact lt_asymm (strict e f edge) rev
  · intro e f edge
    fin_cases e <;> fin_cases f <;> simp_all [feedbackC, fbMoves, fbClock, feedbackBearer, fbRespect]
  · intro t y x r h
    simp only [fbMoves, fbMoved] at *
    rcases h with ⟨a, _, b, c⟩ | ⟨a, _, b, c⟩
    · exact Or.inl ⟨a, b, c⟩
    · exact Or.inr ⟨a, b, c⟩
  · intro t x r h
    exact Or.inl h
  · intro t y x r h
    simp only [fbMoves, fbActual] at *
    rcases h with ⟨a, b, _, c⟩ | ⟨a, b, _, c⟩
    · exact Or.inl ⟨a, b, c⟩
    · exact Or.inr ⟨a, b, c⟩
  · rintro t x r ⟨act, pot⟩
    simp only [fbActual, fbPotency, fbMoved] at *
    rcases act with ⟨a, b, c⟩ | ⟨a, b, c⟩ <;>
      rcases pot with (⟨d, e, f⟩ | ⟨d, e, f⟩) | ⟨d, e, f⟩ <;> simp_all
  · intro t x r h
    simp only [fbMoved, fbMoves] at *
    rcases h with ⟨a, b, c⟩ | ⟨a, b, c⟩
    · exact ⟨false, Or.inl ⟨a, rfl, b, c⟩⟩
    · exact ⟨true, Or.inr ⟨a, rfl, b, c⟩⟩
  · intro t y x r ne h ⟨r', moved⟩
    simp only [fbMoved, fbMoves] at *
    rcases h with ⟨a, b, c, _⟩ | ⟨a, b, c, _⟩ <;>
      rcases moved with ⟨d, e, _⟩ | ⟨d, e, _⟩ <;> simp_all
  · intro _ _ _ h
    exact h.elim
  · rintro ⟨f, ⟨t, x, r, mv⟩, un⟩
    cases f
    · exact un 2 true (Or.inr ⟨rfl, rfl, rfl⟩)
    · exact un 1 false (Or.inl ⟨rfl, rfl, rfl⟩)
  · intro h
    exact h false first1 true (Or.inr ⟨rfl, rfl, rfl⟩)

theorem descent :
    LocalRoutePremises dClock id (fun _ => ()) dC dMoves dMoved dActual dMoved
      (fun _ _ _ => False) ∧
    StrictForward dClock dC ∧
    (∀ n : ℕ, IsFirstUnmovedMover (dMoved (dClock n)) (dMoves (dClock n)) (n + 1)) ∧
    (∀ e, ∃ f, dC f e) ∧ ¬ WellFounded dC := by
  have strict : StrictForward dClock dC := by
    intro e f edge
    simp only [dClock, dC] at *
    omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, strict, ?_, fun e => ⟨e + 1, rfl⟩, ?_⟩
  · intro e f edge rev
    exact lt_asymm (strict e f edge) rev
  · intro e f edge
    exact ⟨rfl, edge⟩
  · intro t y x r h
    exact h.1
  · intro t x r h
    exact h
  · intro t y x r h
    simp only [dActual]
    obtain ⟨a, b⟩ := h
    subst b
    push_cast
    omega
  · rintro t x r ⟨act, pot⟩
    simp only [dActual, dMoved] at *
    omega
  · intro t x r h
    exact ⟨x + 1, h, rfl⟩
  · intro t y x r ne h ⟨r', moved⟩
    simp only [dMoves, dMoved] at *
    obtain ⟨a, _⟩ := h
    apply ne
    omega
  · intro _ _ _ h
    exact h.elim
  · intro n
    refine ⟨⟨n, (), rfl, rfl⟩, ?_⟩
    intro r h
    simp only [dMoved, dClock] at h
    omega
  · intro wf
    have noneAt : ∀ x, Acc dC x → False := by
      intro x acc
      induction acc with
      | intro x _ ih => exact ih (x + 1) rfl
    exact noneAt 0 (wf.apply 0)

theorem circle :
    LocalRoutePremises circleClock id id circleC circleMoves circleMoved circleActual
      circlePotency circleLink ∧
    HasSimultaneous circleClock circleC ∧
    SomethingIsMovedReading (circleMoved 0) ∧
    ¬ NoInfinitePerSeMoverSeriesReading (circleLink 0) ∧
    ¬ FirstUnmovedMoverCannotBeLackingReading (circleMoved 0) (circleMoves 0) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨false, true, by simp [circleC], rfl⟩,
    ⟨false, false, rfl, rfl⟩, ?_, ?_⟩
  · intro e f _ rev
    simp [circleClock] at rev
  · intro e f edge
    exact ⟨rfl, edge, rfl⟩
  · rintro t y x r ⟨a, _, c⟩
    exact ⟨a, c⟩
  · rintro t x r ⟨a, c⟩
    exact Or.inl ⟨a, c⟩
  · rintro t y x r ⟨a, ne, c⟩
    exact Or.inl ⟨a, by subst c; exact fun h => ne h.symm⟩
  · rintro t x r ⟨act, pot⟩
    rcases act with ⟨a, b⟩ | a <;> rcases pot with ⟨c, d⟩ | c
    · exact b d
    · omega
    · omega
    · omega
  · rintro t x r ⟨a, c⟩
    exact ⟨!x, a, by cases x <;> simp, c⟩
  · rintro t y x r ne ⟨a, _, _⟩ _
    exact ⟨a, ne⟩
  · rintro t y x ⟨a, ne⟩
    exact ⟨y, x, ne, rfl, rfl, by simp [circleClock, a], by simp [circleClock, a]⟩
  · intro reg
    have noneAt : ∀ x, Acc (circleLink 0) x → False := by
      intro x acc
      induction acc with
      | intro x _ ih => exact ih (!x) ⟨rfl, by cases x <;> simp⟩
    exact noneAt false (reg false)
  · intro h
    apply h
    rintro ⟨f, ⟨x, r, ⟨_, ne, c⟩⟩, un⟩
    exact un f ⟨rfl, rfl⟩ |>.elim

theorem chain :
    LocalRoutePremises chainClock id id chainC chainMoves chainMoved chainActual chainMoved
      chainLink ∧
    RegressIfSimultaneous chainClock chainC chainLink ∧
    HasSimultaneous chainClock chainC ∧
    IsFirstUnmovedMover (chainMoved 0) (chainMoves 0) 0 := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ⟨0, 1, rfl, rfl⟩, ⟨⟨1, 1, rfl, rfl, rfl⟩, ?_⟩⟩
  · intro e f _ rev
    simp [chainClock] at rev
  · intro e f edge
    exact ⟨rfl, edge, rfl⟩
  · rintro t y x r ⟨a, b, c⟩
    exact ⟨a, c, by omega⟩
  · intro t x r h
    exact h
  · rintro t y x r ⟨a, b, c⟩
    subst c
    exact ⟨a, b⟩
  · rintro t x r ⟨⟨_, a⟩, ⟨_, c, _⟩⟩
    subst c
    omega
  · rintro t x r ⟨a, c, d⟩
    subst c
    have hr := r.isLt
    refine ⟨⟨r.val - 1, by omega⟩, a, ?_, rfl⟩
    simp only
    omega
  · rintro t y x r ne ⟨a, b, _⟩ ⟨r', _, c, d⟩
    subst c
    have hx := x.isLt
    exact ⟨a, by omega, by omega⟩
  · rintro t y x ⟨a, b, c⟩
    exact ⟨y, x, by simp [chainC]; omega, rfl, rfl, a.symm, a.symm⟩
  · intro _ t x
    have wf : WellFounded (chainLink t) := by
      refine Subrelation.wf (r := (· < · : Fin 3 → Fin 3 → Prop)) ?_ wellFounded_lt
      rintro y x ⟨_, b, c⟩
      exact Fin.lt_def.mpr (by omega)
    exact wf.apply x
  · rintro r ⟨_, c, d⟩
    subst c
    exact d rfl

theorem controls : TruthCore.Causality.TemporalPrimaVia.Controls :=
  ⟨conflict, feedback, descent, circle, chain⟩
end TruthCore.Results.Causality.TemporalPrimaVia.Controls
