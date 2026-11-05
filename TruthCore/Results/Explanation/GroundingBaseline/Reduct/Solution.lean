module

public import TruthCore.Explanation.GroundingBaseline.Reduct

@[expose] public section
namespace TruthCore.Results.Explanation.GroundingBaseline.Reduct
open TruthCore.Explanation.GroundingBaseline
open TruthCore.Explanation.GroundingBaseline.Reduct
/-- Shared reduct factorization, not a theorem about queries with a ground argument. -/
theorem invariant : GeneralInvariant := by
  intro W B M N h query
  have ha : M.ontic.frame.access = N.ontic.frame.access :=
    funext (fun w => funext (fun v => propext (h.1 w v)))
  have he : M.ontic.ExistsAt = N.ontic.ExistsAt :=
    funext (fun w => funext (fun b => propext (h.2 w b)))
  rw [ha, he]
end TruthCore.Results.Explanation.GroundingBaseline.Reduct
