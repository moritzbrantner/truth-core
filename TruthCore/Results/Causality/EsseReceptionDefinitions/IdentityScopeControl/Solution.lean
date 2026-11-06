module

public import TruthCore.Causality.EsseReceptionDefinitionFork

@[expose] public section
namespace TruthCore.Results.Causality.EsseReceptionDefinitions.IdentityScopeControl
open TruthCore.Causality.EsseReception
open TruthCore.Causality.EsseReceptionDefinitionFork
open TruthCore.Latin.Aquinas.DeEnte
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.InfinityReception

/-- Frozen exact scope obligation; source claims and original Challenges remain unchanged. -/
theorem identityScopeControl : IdentityScopeControl := by
  have h21 : role2 ≠ role1 := by
    intro h
    have hv : (2 : Nat) = 1 := congrArg Fin.val h
    exact Nat.noConfusion (Nat.succ.inj hv)
  have h01 : role0 ≠ role1 := by
    intro h
    have hv : (0 : Nat) = 1 := congrArg Fin.val h
    exact Nat.noConfusion hv
  refine ⟨True.intro, (fun _ => rfl), rfl, ?_, ?_, ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro s h e hu hc he
    exact ⟨rfl, rfl⟩
  · exact h21
  · intro h
    exact h21 (h false role2 ⟨rfl, rfl⟩)
  · intro x r hi hr
    cases x with
    | false => exact False.elim (h01 hi)
    | true => exact False.elim (Bool.noConfusion hr.1)
  · exact ⟨true, rfl⟩

end TruthCore.Results.Causality.EsseReceptionDefinitions.IdentityScopeControl
