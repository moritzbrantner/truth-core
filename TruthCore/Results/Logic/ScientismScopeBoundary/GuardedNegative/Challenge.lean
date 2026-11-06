module
public import TruthCore.Logic.ScientismScopeBoundary
@[expose] public section
namespace TruthCore.Results.Logic.ScientismScopeBoundary.GuardedNegative
open TruthCore.Logic.Scientism
open TruthCore.Logic.ScientismScopeBoundary
theorem guardedNegative {Claim : Type} (E : EpistemicFrame Claim) (scope : Claim → Prop)
    (hNorm : ScopedScientism E scope)
    (hScope : SomeNonEmpiricalWitnessInScope E scope) : NoNonEmpiricalEstablished E := by
  sorry
end TruthCore.Results.Logic.ScientismScopeBoundary.GuardedNegative
