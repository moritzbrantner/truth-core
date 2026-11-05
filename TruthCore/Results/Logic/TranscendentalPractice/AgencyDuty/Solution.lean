module

public import TruthCore.Logic.TranscendentalPractice

@[expose] public section

namespace TruthCore.Results.Logic.TranscendentalPractice.AgencyDuty

open TruthCore.Logic.TranscendentalPractice

/-- Derive performance from the realized end and uniqueness of the effective
means, then check a joint, nonvacuous two-action model pair differing only in
the categorical-duty assignment. -/
theorem boundary : AgencyDutyBoundary := by
  constructor
  · intro Goal Action P g a hRealized hOnly
    obtain ⟨b, hPerformed, hEffective⟩ := hRealized.2
    have hSame : b = a := hOnly.2 b hEffective
    simpa only [hSame] using hPerformed
  · refine ⟨⟨True.intro, ⟨true, rfl, rfl⟩⟩,
      ⟨True.intro, ⟨true, rfl, rfl⟩⟩,
      ⟨rfl, fun b hb => hb⟩,
      ⟨rfl, fun b hb => hb⟩,
      (fun _ => Iff.rfl),
      (fun _ => Iff.rfl),
      (fun _ _ => Iff.rfl),
      ⟨rfl, rfl⟩, ?_⟩
    exact fun h => Bool.noConfusion h.1

end TruthCore.Results.Logic.TranscendentalPractice.AgencyDuty
