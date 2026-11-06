import TruthCore.Ontology.Naturalism
namespace TruthCore.Results.Ontology.Naturalism.N1EntailsN2
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Ontology.Naturalism
/-- N1 entails N2: if everything existing at `w` satisfies the thesis
predicate, so does everything existing and concrete. -/
theorem n1EntailsN2 {W B : Type} (o : Ontic W B) (concrete P : B → Prop) (w : W)
    (hN1 : ExistenceNaturalism o P w) : ConcreteNaturalism o concrete P w := by
  sorry
end TruthCore.Results.Ontology.Naturalism.N1EntailsN2
