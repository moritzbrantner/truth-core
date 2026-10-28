import TruthCore.Modal.ActualistDomainsCertificate
namespace TruthCore.Results.Modal.ActualistDomains
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Modal.ActualistDomains
variable {W B : Type}
theorem boxAllToAllBox_iff (m : Ontic W B) :
    BoxAllToAllBox m ↔ IncreasingDomains m := by
  constructor
  · intro h w v hAccess x hHere
    exact h (fun u y => m.ExistsAt u y) w (fun _ _ _ hy => hy)
      x hHere v hAccess
  · intro h P w hBox x hHere v hAccess
    exact hBox v hAccess x (h w v hAccess x hHere)

theorem allBoxToBoxAll_iff (m : Ontic W B) :
    AllBoxToBoxAll m ↔ DecreasingDomains m := by
  constructor
  · intro h w v hAccess x hThere
    exact h (fun _ y => m.ExistsAt w y) w (fun _ hy _ _ => hy)
      v hAccess x hThere
  · intro h P w hAll v hAccess x hThere
    exact hAll x (h w v hAccess x hThere) v hAccess

theorem increasing_excludes_contingency (m : Ontic W B)
    (h : IncreasingDomains m) : ∀ w x, ¬ ContingentAt m w x := by
  intro w x hc
  obtain ⟨hx, v, hv, hn⟩ := hc
  exact hn (h w v hv x hx)

theorem checks : ActualistDomainCertificate := by
  refine ⟨fun _ _ m => boxAllToAllBox_iff m,
    fun _ _ m => allBoxToBoxAll_iff m,
    fun _ _ m => increasing_excludes_contingency m, ?_⟩
  let m := TruthCore.Models.PSR.ContingentOnly.model.ontic
  have hPresent : m.ExistsAt false true := Or.inr ⟨rfl, rfl⟩
  have hAbsent : ¬ m.ExistsAt true true := by
    intro h
    rcases h with h | ⟨h, _⟩
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  have hNotIncreasing : ¬ IncreasingDomains m := by
    intro h
    exact hAbsent (h false true True.intro true hPresent)
  have hNotDecreasing : ¬ DecreasingDomains m := by
    intro h
    exact hAbsent (h true false True.intro true hPresent)
  exact ⟨fun _ _ => True.intro, fun _ _ => Or.inl rfl,
    TruthCore.Models.PSR.ContingentOnly.evaluation2,
    hNotIncreasing, hNotDecreasing,
    fun h => hNotIncreasing ((boxAllToAllBox_iff m).mp h),
    fun h => hNotDecreasing ((allBoxToBoxAll_iff m).mp h)⟩
end TruthCore.Results.Modal.ActualistDomains
