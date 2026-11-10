module

public import TruthCore.Causality.SurveyProductiveSource
public import TruthCore.Results.Causality.PossibleCausalSourceNecessity.Solution

@[expose] public section
namespace TruthCore.Results.Causality.SurveyProductiveSource
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.SurveyProductiveSource
open TruthCore.Causality.PossibleCausalSourceNecessity
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)
open TruthCore.Causality.BruteFoundationBoundary (Profile NecessaryConcreteAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)

/-- Reuse the ordinary sameSource consequence, then classify its SAME c from
its outgoing production at v. Necessity and existence are retained at w;
sourcehood and production are asserted only at v. All seven inputs remain open.
No ontic/own-nature necessity or source capability interpretation follows. -/
theorem necessaryConcrete {W B : Type} (p : Profile W B) (w : W)
    (em : ExcludedMiddle) (causal : LocalCausalPrinciple p.ontic)
    (euclidean : Euclidean p.ontic.frame) (reflexive : ActualReflexive p.ontic w)
    (opportunity : PossiblyFailedHeadlessCoverage p.ontic w)
    (productive : ProductiveSources p.ontic w)
    (calibration : AccessibleCausersConcrete p.ontic p.concrete w) :
    NecessaryConcreteAt p w := by
  obtain ⟨v, access, c, present, source, _, actual, necessary⟩ :=
    PossibleCausalSourceNecessity.sameSource p.ontic w em causal euclidean reflexive opportunity
  obtain ⟨y, edge⟩ := productive v access c present source
  exact ⟨c, calibration v access c y edge, actual, necessary⟩

/-- The same four nonlogical source inputs hold for every audit profile. -/
theorem controlBackground (edge concrete : Prop) :
    LocalCausalPrinciple (control edge concrete).ontic ∧
    Euclidean (control edge concrete).ontic.frame ∧
    ActualReflexive (control edge concrete).ontic () ∧
    PossiblyFailedHeadlessCoverage (control edge concrete).ontic () := by
  refine ⟨?_, fun _ _ _ _ _ => True.intro, True.intro, (), True.intro, ?_⟩
  · intro v c h
    obtain ⟨z, _, absent⟩ := h.2
    exact (absent True.intro).elim
  · intro all
    have cone := all ⟨true, True.intro⟩
    obtain ⟨y, hy⟩ := cone ⟨true, True.intro⟩ .refl
    exact Bool.noConfusion hy.2.2.2

private theorem productiveControl (q : Prop) :
    ProductiveSources (control True q).ontic () := by
  intro v _ c _ source
  cases c with
  | true => exact ⟨false, True.intro, rfl, rfl⟩
  | false => exact (source ⟨true, True.intro, True.intro, rfl, rfl⟩).elim

/-- Omitting productivity permits an isolated source; omitting calibration
permits a productive nonconcrete source. Both clauses hold with a concrete
productive source. Finite relative satisfiability, not independent warrant. -/
theorem controls : Controls := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨productiveControl False, ?_, ?_⟩,
    productiveControl True, ?_, ?_⟩
  · intro v _ x y h; exact h.1.elim
  · intro h
    obtain ⟨y, edge⟩ := h () True.intro true True.intro (fun ⟨_, _, h⟩ => h.1)
    exact edge.1
  · rintro ⟨_, h, _⟩; exact h
  · intro h; exact h () True.intro true false ⟨True.intro, rfl, rfl⟩
  · rintro ⟨_, h, _⟩; exact h
  · intro _ _ _ _ _; trivial
  · exact ⟨true, True.intro, True.intro, fun _ _ => True.intro⟩

end TruthCore.Results.Causality.SurveyProductiveSource
