module

public import TruthCore.Causality.EventIdentityProfiles

@[expose] public section

namespace TruthCore.Results.Causality.EventIdentityProfiles.AccessibleTransport

open TruthCore.Causality.EventIdentityProfiles

/-- Corrected conditional transport: uniqueness only among occurrences occurring
at an accessible world. The uniqueness and conditioning antecedents are not proved. -/
theorem accessibleTransport : AccessibleSameEventTransport := by
  intro B T S W C r access occurs condition w e unique h
  exact accessible_same_event_condition access occurs condition w e unique h

/-- Strength comparison, separating nonvacuity witness and omission controls. -/
theorem controls : AccessibleTransportControls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hacc B T S W C r access occurs condition w e unique h
    exact hacc B T S W C r access occurs condition w e
      (global_unique_accessible access occurs w e unique) h
  · intro B T S W r access occurs w e hu he
    exact unique_realization_accessible access occurs w e hu he
  · intro B T S r e unique
    exact global_unique_collapses e unique
  · refine ⟨rfl, repeated_transition_control.2.1, ?_, ?_, ?_, ?_⟩
    · rintro f ⟨_, _, rfl⟩ _
      rfl
    · intro h
      exact repeated_transition_control.2.1 (h (repeatEvent false) rfl)
    · exact ⟨repeatEvent true, rfl, (), True.intro, rfl, (), rfl⟩
    · exact ⟨(), True.intro, rfl, (), rfl⟩
  · intro h
    exact repeated_transition_control.2.2.2
      (h Bool Bool Bool Unit Unit _ (fun _ _ => True) (fun _ _ => True)
        (fun _ _ e => e.bearer = true) () (repeatEvent false)
        ⟨repeatEvent true, rfl, repeated_transition_control.2.2.1⟩)
  · intro h
    obtain ⟨_, _, hf, _⟩ :=
      h Bool Bool Bool Unit Unit _ (fun _ _ => True) (fun _ _ => False)
        (fun _ _ _ => True) () (repeatEvent false)
        (fun _ ⟨_, _, hf⟩ _ => hf.elim)
    exact hf

end TruthCore.Results.Causality.EventIdentityProfiles.AccessibleTransport
