module

public import TruthCore.Logic.Verificationism
public import TruthCore.Results.Logic.Verificationism.Ayer1936Trivial.Solution

@[expose] public section

namespace TruthCore.Results.Logic.Verificationism.Ayer1936Exclusion
open TruthCore.Logic.Verificationism
/-- No 1936 frame excludes a sentence whose negation does not entail some observation statement. -/
theorem ayer1936ExclusionFails : Ayer1936ExclusionFails := by
  intro L F ⟨m, o, ho, hno, hnv⟩
  exact hnv (Ayer1936Trivial.ayer1936CriterionTrivial L F o m ho hno)
end TruthCore.Results.Logic.Verificationism.Ayer1936Exclusion
