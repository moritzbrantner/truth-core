import TruthCore.Causality.NecessaryRootFork

/-! Unicity of actual concrete roots of one selected grounding relation.
Unlike UniqueNecessaryActualRootAt, this endpoint asserts no modal necessity. -/
namespace TruthCore.Causality.ActualRootUniqueness
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualRoot)

/-- Some actual concrete root exists and every actual concrete root at THIS
world of THIS relation equals it. No all-necessary or cross-world claim. -/
def UniqueActualRootAt {W B : Type} (m : Profile W B) (w : W) : Prop :=
  ∃ n, ActualRoot m w n ∧ ∀ x, ActualRoot m w x → x = n

end TruthCore.Causality.ActualRootUniqueness
