module

public import TruthCore.Causality.EventIdentityProfiles

@[expose] public section

namespace TruthCore.Results.Causality.EventIdentityProfiles

open TruthCore.Causality.EventIdentityProfiles

/-- Conditional transport only; the local uniqueness assumption is not proved. -/
theorem transport : SameEventTransport := by
  intro B T S W C r access occurs condition w e unique h
  exact same_event_condition access occurs condition w e unique h

end TruthCore.Results.Causality.EventIdentityProfiles
