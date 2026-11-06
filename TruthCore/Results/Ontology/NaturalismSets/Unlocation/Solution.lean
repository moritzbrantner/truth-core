module

public import TruthCore.Ontology.NaturalismSets

@[expose] public section

namespace TruthCore.Results.Ontology.NaturalismSets
open TruthCore.Ontology.NaturalismSets TruthCore.Ontology.Naturalism
open TruthCore.Ontology.Spatiotemporal
open TruthCore.German.Kant.CosmologicalInference (Ontic)

theorem unlocated {B S : Type} (decode : S → ZFSet.{0}) (F : Frame (B ⊕ S))
    (h : SetLocationHasMemberSupport decode F) : SetRepresentativesUnlocated F := by
  have all : ∀ z : ZFSet.{0}, ∀ s, decode s = z → ¬ Located F (.inr s) := by
    intro z
    refine ZFSet.inductionOn (p := fun z => ∀ s, decode s = z → ¬ Located F (.inr s)) z ?_
    intro z ih s hs hloc
    obtain ⟨t, hm, ht⟩ := h s hloc
    exact ih (decode t) (hs ▸ hm) t rfl ht
  intro s
  exact all (decode s) s rfl

end TruthCore.Results.Ontology.NaturalismSets
