module

public import TruthCore.Causality.ActualEuclidean
public import TruthCore.Results.Causality.InertEmptiness.Solution
public import TruthCore.Results.Causality.LocalFramePossibleExternalCause.Solution

@[expose] public section

namespace TruthCore.Results.Causality.ActualEuclidean
open TruthCore.Causality.ActualEuclidean
open TruthCore.Causality.InertEmptiness (EmptinessStaysEmpty PossiblyContingentsAbsentThenPresent)
open TruthCore.Causality.SpineRivalsStageOne.Control (Place)
open TruthCore.Causality.BruteFoundationBoundary (NecessaryConcreteAt)
open TruthCore.Causality.CountTemporalNecessity (HistoryPresenceActual)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Causality.PossibleCauseOfContingency
  (Scenario PossiblyBeginsAt CausalOpportunityAt)
open TruthCore.Modal (Euclidean)
open TruthCore.Modal.TemporalHistory (History)

/-- Strength order: global Euclidean access gives Euclidean access at any world. -/
theorem euclideanAtOfEuclidean {W : Type} (frame : TruthCore.Modal.Frame W) (w : W)
    (hEuclidean : Euclidean frame) : EuclideanAt frame w :=
  fun v z hwv hwz => hEuclidean w v z hwv hwz

/-- The inert-emptiness arrival with Euclidean access required only at the
selected world. Reuses `earlierNecessary` for the accessible history. -/
theorem inertNecessaryConcrete {W B T : Type} [Preorder T] (h : History W B T)
    (Concrete : B → Prop) (G : W → B → B → Prop) (w : W)
    (hEuclidean : EuclideanAt h.ontic.frame w)
    (hReflexive : ActualReflexive h.ontic w)
    (hPresence : HistoryPresenceActual h)
    (hInert : EmptinessStaysEmpty h Concrete)
    (hPossible : PossiblyContingentsAbsentThenPresent h Concrete w) :
    NecessaryConcreteAt ⟨h.ontic, Concrete, G⟩ w := by
  obtain ⟨v, hwv, hBegins⟩ := hPossible
  obtain ⟨c, hc, _, hNecessary⟩ :=
    TruthCore.Results.Causality.InertEmptiness.earlierNecessary h Concrete v
      hPresence hInert hBegins
  exact ⟨c, hc, necessaryAtOrigin h.ontic w v c hEuclidean hReflexive hwv hNecessary⟩

/-- The possible-external-cause arrival with Euclidean access required only at
the selected world. Reuses `necessaryOfExternalCandidate` for the same cause. -/
theorem externalNecessaryConcrete {W B : Type} (s : Scenario W B) (w : W)
    (hEuclidean : EuclideanAt s.ontic.frame w)
    (hReflexive : ActualReflexive s.ontic w)
    (hBeginning : PossiblyBeginsAt s w)
    (hOpportunity : CausalOpportunityAt s w) :
    TruthCore.Causality.PossibleCauseOfContingency.NecessaryConcreteAt s w := by
  obtain ⟨v, hwv, _, c, hc, he, _, hOutside⟩ := hOpportunity hBeginning
  have hNecessary :=
    TruthCore.Causality.LocalFramePossibleExternalCause.necessaryOfExternalCandidate
      s v c hc he hOutside
  exact ⟨c, hc, necessaryAtOrigin s.ontic w v c hEuclidean hReflexive hwv hNecessary⟩

/-- The separating model and the stepwise status, by case analysis. -/
theorem controls : Control.Certificate := by
  refine ⟨⟨?_, Or.inl rfl, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro v z hv hz
    cases v <;> cases z <;> simp_all [Control.clustered]
  · intro hE
    have h := hE Place.near Place.far Place.near (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (Or.inl rfl)
    simp [Control.clustered] at h
  · intro v x t hp
    rcases hp with hx | hx
    · exact Or.inl hx
    · exact Or.inr ⟨hx.1, hx.2.1⟩
  · intro v s t _ hEmpty
    exact absurd (Or.inl rfl) (hEmpty false trivial)
  · refine ⟨Place.near, Or.inr (Or.inl ⟨rfl, rfl⟩), 0, 1, Nat.zero_lt_one, ?_, true, trivial,
      ⟨Or.inr ⟨rfl, rfl⟩, Place.far, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩,
      Or.inr ⟨rfl, rfl, rfl⟩⟩
    · intro x _ hCont hxs
      rcases hxs with hx | hx
      · subst hx
        obtain ⟨_, u, _, hAbsent⟩ := hCont
        exact hAbsent (Or.inl rfl)
      · exact absurd hx.2.2 (by decide)
    · rintro (h | ⟨_, h⟩) <;> cases h
  · intro hE
    have h := hE Place.near Place.actual (Or.inr (Or.inl ⟨rfl, rfl⟩)) (Or.inl rfl)
    simp [TruthCore.Causality.SpineRivalsStageOne.Control.stepwise] at h

end TruthCore.Results.Causality.ActualEuclidean
