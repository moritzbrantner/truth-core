import TruthCore.Metaethics.AdoptionReasons

namespace TruthCore.Results.Metaethics.AdoptionReasons
open TruthCore.Logic.EpistemicReasons
open TruthCore.Metaethics.AdoptionReasons

/-- A denial of all reasons of one kind applies to adoption of the view. -/
theorem kindDenialLeavesAdoptionGap {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (kind : Kind) (view : Target)
    (hDenial : NoReasonsOfKind reason kind) :
    NoInternalAdoptionReason reason kind view := by
  sorry

/-- A denial across all represented kinds leaves an adoption gap in every kind. -/
theorem globalDenialLeavesAdoptionGap {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (view : Target)
    (hDenial : GlobalNormativeNihilism reason) :
    NoInternalAdoptionReasonOfAnyKind reason view := by
  sorry

/-- The global denial is incompatible with a witness for the existing F6
proposition when its reason relation is the epistemic kind in this profile. -/
theorem epistemicReasonExcludesGlobalDenial {Kind Agent Target : Type}
    (reason : Kind → Agent → Target → Prop) (epistemic : Kind)
    (hEpistemic : ThereAreEpistemicReasons (reason epistemic)) :
    GlobalNormativeNihilismExcluded reason := by
  sorry

/-- The restriction to one kind matters. In this profile the epistemic reason
for the selected target exists even though the moral relation is empty. -/
theorem moralDenialAllowsEpistemicAdoption :
    MoralDenialEpistemicAdoptionControl := by
  sorry

end TruthCore.Results.Metaethics.AdoptionReasons
