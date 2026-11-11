import TruthCore.Causality.SpineRivalsRootEsse

/-!
Rival survival certificates for twelve spine premises. Each registered theorem
checks one explicit interpretation: the rival holds together with every other
premise of the named consuming theorem, and that theorem's conclusion fails.
The unregistered `…_excludes` helpers show that each rival is incompatible with
its premise on the shared carrier. Nothing here establishes or refutes a
premise, and no interpretation is claimed metaphysically possible.
-/

namespace TruthCore.Results.Causality.SpineRivalsRootEsse

open TruthCore.Causality.SpineRivalsRootEsse
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Causality.ExistenceActuality (ExistingInActAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround
  SimplyPriorIsActualConcreteGround)
open TruthCore.Causality.WholeRosterFoundation (WholeRosterNotTrapped)
open TruthCore.Causality.DirectEsseRootUniquenessAtBeing (GradesToMaximumAtBeing)
open TruthCore.Causality.NecessarilyUnderived (UnionNecessarySupport)
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Case.Catholicism

/-! ## Each rival is incompatible with its premise -/

/-! ## Survival certificates -/

open Control

theorem abstractOnlySurvives : AbstractOnlySurvives := by
  sorry

theorem bottomlessSurvives : BottomlessSurvives := by
  sorry

theorem contingentRootSurvives : ContingentRootSurvives := by
  sorry

theorem idleMaximumSurvives : IdleMaximumSurvives := by
  sorry

theorem thinExistenceSurvives : ThinExistenceSurvives := by
  sorry

theorem nonConcreteEsseCauseSurvives : NonConcreteEsseCauseSurvives := by
  sorry

theorem unboundedGradesSurvive : UnboundedGradesSurvive := by
  sorry

theorem mereConservationSurvives : MereConservationSurvives := by
  sorry

theorem abstractPriorSurvives : AbstractPriorSurvives := by
  sorry

theorem exceededGodSurvives : ExceededGodSurvives := by
  sorry

theorem contingentSupportSurvives : ContingentSupportSurvives := by
  sorry

theorem mutualSupportSurvives : MutualSupportSurvives := by
  sorry

end TruthCore.Results.Causality.SpineRivalsRootEsse
