module

public import TruthCore.Causality.InertEmptiness

@[expose] public section

namespace TruthCore.Results.Causality.InertEmptiness
open TruthCore.Causality.InertEmptiness
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt)
open TruthCore.Causality.CountTemporalNecessity (HistoryPresenceActual)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)
open TruthCore.Modal (Euclidean)
open TruthCore.Modal.TemporalHistory (History)

/-- In one history: if contingent concrete things are absent at a moment and
one is present later, inert emptiness puts some concrete individual at the
earlier moment. It is none of the contingent ones, so it is absent from no
accessible world. No causal relation between it and anything is concluded. -/
theorem earlierNecessary {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (v : W)
    (hPresence : HistoryPresenceActual h)
    (hInert : EmptinessStaysEmpty h Concrete)
    (hBegins : ContingentsAbsentThenPresentAt h Concrete v) :
    ∃ c, Concrete c ∧ h.ontic.ExistsAt v c ∧ NecessaryAt h.ontic v c := by
  obtain ⟨s, t, hst, hAbsent, x, hx, _, hxt⟩ := hBegins
  have hNotEmpty : ¬ ConcreteEmptyAt h Concrete v s := fun hEmpty =>
    hInert v s t hst hEmpty x hx hxt
  have hSome : ∃ c, Concrete c ∧ h.IsAt v c s := by
    apply Classical.byContradiction
    intro hNone
    exact hNotEmpty fun c hc hcs => hNone ⟨c, hc, hcs⟩
  obtain ⟨c, hc, hcs⟩ := hSome
  have hExists : h.ontic.ExistsAt v c := hPresence v c s hcs
  refine ⟨c, hc, hExists, ?_⟩
  intro u hvu
  apply Classical.byContradiction
  intro hAbsentAtU
  exact hAbsent c hc ⟨hExists, u, hvu, hAbsentAtU⟩ hcs

/-- Stage one of the modal spine without a causal premise. If a history with a
contingent-free moment before a contingent-populated one is accessible, then
under inert emptiness, presence-to-existence and the two frame conditions one
and the same concrete individual exists at `w` and at every world accessible
from `w`. `G` is any grounding relation: the conclusion does not constrain it. -/
theorem necessaryConcrete {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hEuclidean : Euclidean h.ontic.frame)
    (hReflexive : ActualReflexive h.ontic w)
    (hPresence : HistoryPresenceActual h)
    (hInert : EmptinessStaysEmpty h Concrete)
    (hPossible : PossiblyContingentsAbsentThenPresent h Concrete w) :
    NecessaryConcreteAt ⟨h.ontic, Concrete, G⟩ w := by
  obtain ⟨v, hwv, hBegins⟩ := hPossible
  obtain ⟨c, hc, _, hNecessary⟩ := earlierNecessary h Concrete v hPresence hInert hBegins
  exact ⟨c, hc, hNecessary w (hEuclidean w v w hwv hReflexive),
    fun z hwz => hNecessary z (hEuclidean w v z hwv hwz)⟩

/-- Inert emptiness and its rival exclude one another on the same history and
concreteness predicate. -/
theorem inertExcludesPopulatedEmptiness {W B T : Type} [Preorder T]
    (h : History W B T) (Concrete : B → Prop)
    (hInert : EmptinessStaysEmpty h Concrete) :
    ¬ EmptinessBecomesPopulated h Concrete := by
  rintro ⟨v, s, t, hst, hEmpty, x, hx, hxt⟩
  exact hInert v s t hst hEmpty x hx hxt

/-- In the `rooted` control the individual `true` does not exist at world `false`. -/
theorem absentAtFalse : ¬ Control.rooted.ontic.ExistsAt false true :=
  fun e => e.elim (fun a => Bool.noConfusion a) (fun a => Bool.noConfusion a)

/-- Omission and nonvacuity controls on four two-world interpretations with natural-number times. -/
theorem controls : Control.Certificate := by
  refine ⟨⟨fun _ _ _ _ _ => trivial, trivial⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun v _ _ hp => hp.1,
      ⟨true, trivial, 0, 1, Nat.zero_lt_one, ?_, (), trivial,
        ⟨rfl, false, trivial, Bool.false_ne_true⟩, rfl, rfl⟩,
      ⟨true, 0, 1, Nat.zero_lt_one, ?_, (), trivial, rfl, rfl⟩, ?_, ?_⟩
    · intro _ _ _ hp; exact absurd hp.2 (by decide)
    · intro _ _ hp; exact absurd hp.2 (by decide)
    · intro hInert
      exact hInert true 0 1 Nat.zero_lt_one
        (fun _ _ hp => absurd hp.2 (by decide)) () trivial ⟨rfl, rfl⟩
    · rintro ⟨_, _, _, hNec⟩
      exact Bool.false_ne_true (hNec false trivial)
  · refine ⟨fun v _ _ hp => hp, ?_, ?_, ⟨(), rfl, false, trivial, Bool.false_ne_true⟩, ?_⟩
    · intro v s t _ hEmpty x _ hxt
      exact hEmpty x trivial hxt
    · rintro v _ ⟨s, t, _, hAbsent, x, hx, hCont, hxt⟩
      exact hAbsent x hx hCont hxt
    · rintro ⟨_, _, _, hNec⟩
      exact Bool.false_ne_true (hNec false trivial)
  · refine ⟨?_, ?_, ⟨true, trivial, 0, 1, Nat.zero_lt_one, ?_, true, trivial,
      ⟨⟨rfl, rfl⟩, false, trivial, fun e => Bool.false_ne_true e.2⟩,
      Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    · intro hPresence
      exact absurd (hPresence true false 0 (Or.inl rfl)).1 (by decide)
    · intro v s t _ hEmpty
      exact absurd (Or.inl rfl) (hEmpty false trivial)
    · intro x _ hCont hxs
      rcases hxs with hx | hx
      · subst hx; exact absurd hCont.1.1 (by decide)
      · exact absurd hx.2 (by decide)
    · rintro ⟨x, _, hEx, hNec⟩
      exact absurd (hNec false trivial).2 (by decide)
  · refine ⟨?_, ?_, ⟨true, trivial, 0, 1, Nat.zero_lt_one, ?_, true, trivial,
      ⟨Or.inr rfl, false, trivial, absentAtFalse⟩, Or.inr ⟨rfl, rfl⟩⟩,
      ⟨Or.inr rfl, false, trivial, absentAtFalse⟩,
      ⟨false, trivial, Or.inl rfl, fun _ _ => Or.inl rfl⟩⟩
    · intro v c t hp
      rcases hp with hc | hc
      · exact Or.inl hc
      · exact Or.inr hc.1
    · intro v s t _ hEmpty
      exact absurd (Or.inl rfl) (hEmpty false trivial)
    · intro x _ hCont hxs
      rcases hxs with hx | hx
      · subst hx
        obtain ⟨_, u, _, hAbsent⟩ := hCont
        exact hAbsent (Or.inl rfl)
      · exact absurd hx.2 (by decide)

end TruthCore.Results.Causality.InertEmptiness
