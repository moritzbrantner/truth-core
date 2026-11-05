module
public import TruthCore.Results.Explanation.TruthmakerTheories.Solution
@[expose] public section
namespace TruthCore.Results.Explanation.TruthmakerTheories
open TruthCore.Explanation.PSRStrength
open TruthCore.Explanation.DisjunctionGround
open TruthCore.Explanation.TruthmakerTheories

theorem restrictedSeparation : RestrictedSeparation := by
  have hn : ¬ ∃ b, restrictedMaking false b .some := by
    rintro ⟨b, _, h⟩
    exact DFact.noConfusion h
  exact ⟨restrictedCoverage, trivial, hn,
    fun hm => hn (hm.2 false .some trivial trivial)⟩
end TruthCore.Results.Explanation.TruthmakerTheories
