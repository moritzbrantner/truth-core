import Mathlib
import TruthCore.Causality.BruteFoundationBoundary

namespace TruthCore.Results.Causality.BruteRootDisjunction

open TruthCore.Causality.BruteFoundationBoundary

/-- Mathematical conditional only: under classical logic, the assumption
that all concrete individuals at an inhabited actual world are contingent
imposes a genuine choice between a contingent concrete root and a failure
of well-founded grounding. No philosophical PSR, act/potency bridge or
claim of metaphysical possibility is proved. -/
theorem bruteRootDisjunction : BruteRootDisjunctionClaim := by
  intro World Being m w hPop hNoNecessary
  exact bruteRootOrNonWellFounded m w hPop hNoNecessary

end TruthCore.Results.Causality.BruteRootDisjunction
