import TruthCore.Logic.SelfApplication
namespace TruthCore.Results.Logic.SelfApplication.Dilemma
open TruthCore.Logic.SelfApplication
/-- The reusable self-application dilemma, premise-free: a claim in a norm's
scope that fails the norm's standard is either unacceptable (if the norm holds)
or a counterexample to the norm (if it is acceptable). -/
theorem selfApplicationDilemma : SelfApplicationDilemma := by
  intro Claim N Acceptable self hScope hFail
  exact Norm.selfApplication hScope hFail
end TruthCore.Results.Logic.SelfApplication.Dilemma
