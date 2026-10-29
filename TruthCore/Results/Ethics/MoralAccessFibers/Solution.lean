import TruthCore.Ethics.MoralAccessFibers
import TruthCore.Results.Logic.CorrectionCriterion.Solution

namespace TruthCore.Results.Ethics.MoralAccessFibers
open TruthCore.Logic.CorrectionCriterion
open TruthCore.Ethics.MoralAccessFibers

/-- Instantiates the existing exact criterion on the supplied moral question and
restricted classes. This accepts no actual-world moral or epistemic bridge. -/
theorem certificate : Controls := by
  have factor := TruthCore.Results.Logic.CorrectionCriterion.characterization.1
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    have inv := (factor State _ outward Prohibited).mp h
    have bad : false = true := (inv ⟨true, false, false⟩ ⟨true, false, true⟩ rfl).mpr rfl
    cases bad
  · intro h
    have inv := (factor {s // NaturalBasis s} _
      (fun s => outward s.val) (fun s => Prohibited s.val)).mp h
    have bad : false = true :=
      (inv ⟨⟨true, false, false⟩, rfl⟩ ⟨⟨true, true, true⟩, rfl⟩ rfl).mpr rfl
    cases bad
  · apply (factor {s // NaturalBasis s} _
      (fun s => enriched s.val) (fun s => Prohibited s.val)).mpr
    intro s t same
    have basisSame : s.val.basis = t.val.basis := congrArg Prod.snd same
    have truthSame : s.val.prohibited = t.val.prohibited :=
      s.property.trans (basisSame.trans t.property.symm)
    change (s.val.prohibited = true ↔ t.val.prohibited = true)
    rw [truthSame]
  · apply (factor {s // Categorical s} _
      (fun s => outward s.val) (fun s => Prohibited s.val)).mpr
    intro s t _
    exact ⟨fun _ => t.property, fun _ => s.property⟩
  · exact ⟨⟨⟨false, false, true⟩, rfl⟩, rfl, rfl⟩
  · intro s
    exact s.property
  · intro h
    have inv := (factor {s // SufficientBasis s} _
      (fun s => enriched s.val) (fun s => Prohibited s.val)).mp h
    have off : SufficientBasis ⟨true, false, false⟩ := by
      intro impossible
      cases impossible
    have on : SufficientBasis ⟨true, false, true⟩ := by
      intro _
      rfl
    have bad : false = true :=
      (inv ⟨⟨true, false, false⟩, off⟩ ⟨⟨true, false, true⟩, on⟩ rfl).mpr rfl
    cases bad

end TruthCore.Results.Ethics.MoralAccessFibers
