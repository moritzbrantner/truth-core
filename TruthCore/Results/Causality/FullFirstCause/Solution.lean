module

public import TruthCore.Causality.FullFirstCause
public import TruthCore.Results.Causality.PossibleCausalSourceNecessity.Solution

@[expose] public section
namespace TruthCore.Results.Causality.FullFirstCause
open TruthCore.Causality.FullFirstCause
open TruthCore.Causality.WorldSourceRegress

/-- Same-N assembly. All five Prop inputs are explicit; universality of M
is retained in the full input but only its source/outgoing conjuncts are needed.
This is transcription/assembly, not a new argument for full-first-cause existence. -/
theorem necessaryConcrete {W B : Type}
    (p : TruthCore.Causality.BruteFoundationBoundary.Profile W B) (w : W)
    [PartialOrder (Actual p.ontic w)]
    (G : TruthCore.Logic.Regress.Graph (Actual p.ontic w))
    (requirement : Actual p.ontic w → Actual p.ontic w → Prop)
    (em : TruthCore.Logic.ExcludedMiddle)
    (causal : TruthCore.German.Kant.CosmologicalInference.LocalCausalPrinciple p.ontic)
    (dictionary : ActualProductionDictionary p.ontic w G)
    (concrete : TruthCore.Causality.CausalPowerConcreteness.CausersRequireConcreteAt
      p.ontic p.concrete w)
    (full : ExistsFirstCause G requirement) :
    TruthCore.Causality.BruteFoundationBoundary.NecessaryConcreteAt p w := by
  obtain ⟨N, source, M, edge, _⟩ := full
  have actualSource : (actualGraph p.ontic w).Source N := by
    rintro ⟨y, hy⟩
    exact source ⟨y, (dictionary y N).mpr hy⟩
  have necessary := PossibleCausalSourceNecessity.source_necessary_at p.ontic w N.val
    em causal N.property
    ((WorldSourceRegress.actualSource_iff p.ontic w N).mp actualSource)
  exact ⟨N.val, concrete N.val M.val ((dictionary N M).mp edge), N.property, necessary⟩

private theorem source : Fixture.graph.Source .origin := by
  rintro ⟨c, _, he | he⟩ <;> cases he

private theorem noFull (requirement : Fixture.Object → Fixture.Object → Prop)
    (h : ∀ x y, x ≠ .origin → ¬ Prior requirement x y) :
    ¬ ExistsFirstCause Fixture.graph requirement := by
  rintro ⟨N, _, M, ⟨rfl, hM | hM⟩, universal⟩
  · subst M
    rcases universal .other ⟨.origin, rfl, Or.inr rfl⟩ (by decide) with prior | incl
    · exact h .effect .other (by decide) prior
    · cases incl
  · subst M
    rcases universal .effect ⟨.origin, rfl, Or.inl rfl⟩ (by decide) with prior | incl
    · exact h .other .effect (by decide) prior
    · cases incl

theorem comparisons : Comparisons := by
  refine ⟨⟨source, .effect, ⟨rfl, Or.inl rfl⟩, ?_⟩,
    ⟨rfl, Or.inr rfl⟩, by decide, ⟨source, .effect, rfl, Or.inl rfl⟩,
    noFull _ (fun _ _ _ h => h.1), ?_, ?_, ?_, ⟨rfl, Or.inl rfl⟩,
    ⟨rfl, Or.inr rfl⟩, by decide⟩
  · rintro e ⟨c, _, he | he⟩ different
    · exact (different he).elim
    · subst e
      exact Or.inl ⟨⟨rfl, rfl⟩, fun h => by cases h.1⟩
  · intro e ⟨c, _, he⟩
    exact ⟨⟨rfl, he⟩, fun h => by rcases he with he | he <;> subst e <;> cases h.1⟩
  · exact noFull _ (fun x _ hx prior => hx prior.1.1)
  · refine ⟨?_, 2, ⟨rfl, Or.inr rfl⟩, ?_⟩
    · rintro ⟨c, _, he | he⟩
      · exact (by decide : (0 : Fin 3) ≠ 1) he
      · exact (by decide : (0 : Fin 3) ≠ 2) he
    · rintro e ⟨c, _, he | he⟩ different
      · subst e; exact Or.inr (by decide)
      · exact (different he).elim

end TruthCore.Results.Causality.FullFirstCause
