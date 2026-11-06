module
public import TruthCore.Logic.ScientismScopeBoundary
@[expose] public section
namespace TruthCore.Results.Logic.ScientismScopeBoundary.AllToPointwise
open TruthCore.Logic.Scientism
open TruthCore.Logic.ScientismScopeBoundary
theorem allToPointwise {Claim : Type} (E : EpistemicFrame Claim) (scope : Claim → Prop)
    (h : AllEstablishedInScope E scope) : NonEmpiricalWitnessesInScope E scope := by
  sorry
end TruthCore.Results.Logic.ScientismScopeBoundary.AllToPointwise
