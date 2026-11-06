module

public import TruthCore.Causality.DefinitionDictionaryConnections

@[expose] public section

namespace TruthCore.Results.Causality.DefinitionDictionaryConnections

open TruthCore.Causality.DefinitionDictionaryConnections

/-- Dictionary equality and packaging only, with all supplied parameters held
fixed. No frame, population or philosophical interpretation is inferred. -/
theorem connections : Connections := by
  refine ⟨?_, ?_, ?_⟩
  · intro W B m w
    rfl
  · intro W B o w x
    rfl
  · intro B abstract concrete
    constructor
    · intro h
      exact ⟨⟨concrete, abstract, h⟩, rfl, rfl⟩
    · rintro ⟨c, rfl, rfl⟩
      exact c.disjoint

end TruthCore.Results.Causality.DefinitionDictionaryConnections
