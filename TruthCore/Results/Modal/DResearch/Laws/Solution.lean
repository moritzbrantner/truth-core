import TruthCore.Modal.DResearch.Laws
namespace TruthCore.Results.Modal.DResearch.Laws
open TruthCore.Modal
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.DResearch

theorem checks : LawChecks := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro W F D w hSerial hIdentity hMC
    obtain ⟨v, hv⟩ := hSerial w
    have he := identity_separates F D w hIdentity hMC v hv
    exact he ▸ hv
  · intro W F w hSerial
    constructor
    · intro hMC
      have hSep := identity_separates F allPredicates w trivial hMC
      obtain ⟨v, hv⟩ := hSerial w
      exact ⟨hSep v hv ▸ hv, hSep⟩
    · rintro ⟨_, hSep⟩ P _ hp v hv
      exact hSep v hv ▸ hp
  · intro W F D w hSerial hEM hNeg hExt hMC
    obtain ⟨v, hv⟩ := hSerial w
    have he := extensional_separates F D w hEM hNeg hExt hMC v hv
    exact he.symm ▸ hv
  · refine ⟨?_, ?_, ?_⟩
    · intro W F D w P hSerial hMC hP hp
      obtain ⟨v, hv⟩ := hSerial w
      exact ⟨v, hv, hMC P hP hp v hv⟩
    · intro W F D w hSerial hBox
      obtain ⟨v, hv⟩ := hSerial w
      exact ⟨v, hv, hBox v hv⟩
    · intro W F w hSerial hBox
      obtain ⟨v, hv⟩ := hSerial w
      exact hBox v hv
  · intro W F w P hMC ⟨⟨v, hv, hp⟩, ⟨z, hz, hn⟩⟩
    have hSep := identity_separates F allPredicates w trivial hMC
    have hpw : P w := hSep v hv ▸ hp
    have hnw : ¬ P w := hSep z hz ▸ hn
    exact hnw hpw
end TruthCore.Results.Modal.DResearch.Laws
