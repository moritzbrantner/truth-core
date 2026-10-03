import TruthCore.Greek.Aristotle.Physics.BookII.Chapter4

namespace TruthCore.Results.Aristotle.Physics.OrganismCosmosAsymmetry

open TruthCore.Greek.Aristotle.Physics

/-- The reported organism/cosmos assignments create the asymmetry Aristotle highlights. -/
theorem predecessorOrganismCosmosAsymmetry
    (OrganismsComeToBeByChance OrganismsHaveNatureMindOrSimilarCause
      SeedKindsYieldRegularOutcomes CosmosArisesFromSpontaneity
      CosmosHasOrganismLikeCause CausalAsymmetryRequiresExplanation : Prop)
    (hOrganisms :
      AttributedOrganismsNotFromChanceReading
        OrganismsComeToBeByChance OrganismsHaveNatureMindOrSimilarCause
        SeedKindsYieldRegularOutcomes)
    (hCosmos :
      AttributedCosmosFromSpontaneityReading
        CosmosArisesFromSpontaneity CosmosHasOrganismLikeCause)
    (hAsymmetry :
      OrganismCosmosAsymmetryRequiresExplanationReading
        OrganismsComeToBeByChance CosmosArisesFromSpontaneity
        CausalAsymmetryRequiresExplanation) :
    PredecessorOrganismCosmosAsymmetryReading
      CausalAsymmetryRequiresExplanation := by
  exact hAsymmetry ⟨hOrganisms.1, hCosmos.1⟩

end TruthCore.Results.Aristotle.Physics.OrganismCosmosAsymmetry
