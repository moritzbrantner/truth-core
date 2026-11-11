module
public import TruthCore.Causality.Power1392
@[expose] public section
namespace TruthCore.Results.Causality.Power1392
open TruthCore.Causality.Power1392
open TruthCore.Causality.NamingVeracityBatch1

theorem certificate : Certificate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ P
    constructor
    · rintro ⟨ability, hPower, hSafe⟩ x t hReq
      exact hSafe x t (hPower x t hReq)
    · intro h
      exact ⟨AllReq σ P, (fun _ _ hReq => hReq), h⟩
  · intro σ P Infinite g hg hUnlimited hPower hPossible hSafe t
    constructor
    · exact hPossible t
    · intro hReq
      exact hSafe g t (hPower g t (fun r hr => hUnlimited g hg r (hReq r hr)))
  · intro σ P feasible g hRealize hSafety
    exact ⟨fun h t ht => hSafety t (h t ht), fun h t ht => hRealize t (h t ht)⟩
  · constructor
    · exact ⟨_, Control.jP, Control.jInfinite, true, rfl,
        (fun _ hx _ _ => hx), (fun _ _ h => h () trivial),
        (fun _ _ _ _ => trivial), (fun _ _ _ => trivial), trivial, rfl⟩
    · refine ⟨_, Control.power True True (fun p => p) True (fun _ => False),
        (fun _ _ => False), true, (fun _ h => h.elim), (fun _ h => h), ?_⟩
      intro h
      exact h () trivial
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨(fun h => (h rfl).elim), (fun _ _ _ h => h () trivial),
        (fun _ _ h => h.elim), (fun _ _ _ h => h.elim),
        (fun h => h.mpr (fun _ _ => trivial))⟩
    · exact ⟨(fun _ _ _ _ _ => trivial), (fun h => (h rfl).elim),
        (fun _ _ h => h.elim), (fun _ _ _ h => h.elim),
        (fun h => h.mpr (fun _ _ => trivial))⟩
    · exact ⟨(fun _ _ _ _ h => h.elim), (fun _ _ _ _ => trivial),
        (fun h => (h rfl).elim), (fun _ _ _ _ => trivial),
        (fun h => h.mp trivial () trivial)⟩
    · exact ⟨(fun _ _ _ _ _ => trivial), (fun _ _ _ _ => trivial),
        (fun _ _ h => h.elim), (fun h => (h rfl).elim),
        (fun h => h.mpr (fun _ _ => trivial))⟩
end TruthCore.Results.Causality.Power1392
