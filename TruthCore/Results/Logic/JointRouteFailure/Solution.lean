module

public import TruthCore.Logic.JointRouteFailure

@[expose] public section

namespace TruthCore.Results.Logic.JointRouteFailure

open TruthCore.Logic

/-- The checked logical rule template, with its decision principle explicit. -/
theorem rootFromJointFailureIncompatibility (hEM : ExcludedMiddle) :
    TruthCore.Logic.JointRouteFailure.RootFromJointFailureIncompatibility :=
  TruthCore.Logic.JointRouteFailure.rootFromJointFailureIncompatibility hEM

end TruthCore.Results.Logic.JointRouteFailure
