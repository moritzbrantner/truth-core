module

public import TruthCore.Causality.MaximalGroundingAsymmetry

@[expose] public section
namespace TruthCore.Results.Causality.MaximalGroundingAsymmetry.Strength
open TruthCore.Causality.MaximalGroundingAsymmetry
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.ExistenceActuality
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryRootUniqueness
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic
open TruthCore.Logic.CogitoConcrete

/-- Analyst same-dictionary scope consequence; all original source/Challenge interfaces preserved. -/
theorem globalImpliesMaximal {W B R : Type} (m : Profile W B) (w : W)
    (InAct : B → R → Prop) (MoreIn : R → B → B → Prop) (esse : R)
    (h : ActualGroundingAsymmetric m w) : AtMaximalTarget m w InAct MoreIn esse := by
  exact fun a b ha hb _ hab => h a b ha hb hab

end TruthCore.Results.Causality.MaximalGroundingAsymmetry.Strength
