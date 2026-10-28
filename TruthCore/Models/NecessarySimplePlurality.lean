import TruthCore.Results.Causality.NecessarySimplePlurality.Solution

/-! Closed finite-model projections of the single joint control. Registration
is model-relative, not source fidelity or metaphysical possibility. The Q11
predicate parameter is the two-root candidate predicate, not an identification
of those candidates with God. -/
namespace TruthCore.Models.NecessarySimplePlurality
open TruthCore.Causality.NecessarySimplePlurality

def model := (power, explanation, esseProfile)
def pureAct := TruthCore.Latin.Aquinas.SummaTheologiae.PureAct moved

theorem enumerateBeing : ∀ x : Being,
    x = .left ∨ x = .right ∨ x = .instrument ∨ x = .effect := by
  intro x
  cases x with
  | left => exact Or.inl rfl
  | right => exact Or.inr (Or.inl rfl)
  | instrument => exact Or.inr (Or.inr (Or.inl rfl))
  | effect => exact Or.inr (Or.inr (Or.inr rfl))

theorem enumerateRespect : ∀ r : Respect, r = .esse ∨ r = .drive ∨ r = .heat := by
  intro r
  cases r with
  | esse => exact Or.inl rfl
  | drive => exact Or.inr (Or.inl rfl)
  | heat => exact Or.inr (Or.inr rfl)

theorem enumerateWorld : ∀ w : Bool, w = false ∨ w = true := by
  intro w
  cases w
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem evaluation0 : @TruthCore.Latin.Aquinas.SummaTheologiae.SomethingIsMovedReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h0

theorem evaluation1 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovedOnlyAsInPotencyReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moved) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h1

theorem evaluation2 : @TruthCore.Latin.Aquinas.SummaTheologiae.MovesOnlyAsInActReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moves) (TruthCore.Causality.NecessarySimplePlurality.inAct) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h2

theorem evaluation3 : @TruthCore.Latin.Aquinas.SummaTheologiae.ReducedOnlyByAMoverReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h3

theorem evaluation4 : @TruthCore.Latin.Aquinas.SummaTheologiae.NotActAndPotencyInSameRespectReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.inAct) (TruthCore.Causality.NecessarySimplePlurality.moved) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h4

theorem evaluation5 : @TruthCore.Latin.Aquinas.SummaTheologiae.SecondMoversMoveOnlyAsMovedReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves) (TruthCore.Causality.NecessarySimplePlurality.asMoved) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h5

theorem evaluation6 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoInfinitePerSeMoverSeriesReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.asMoved) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h6

theorem evaluation7 : @TruthCore.Latin.Aquinas.SummaTheologiae.ActSimplyPriorToPotencyReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.inAct) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.component) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h7

theorem evaluation8 : @TruthCore.Case.Catholicism.FirstUnmovedMoverIsFirstBeing (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves) (TruthCore.Causality.NecessarySimplePlurality.component) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h8

theorem evaluation9 : @TruthCore.Latin.Aquinas.SummaTheologiae.NoBodyMovesUnlessMovedReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves) (TruthCore.Causality.NecessarySimplePlurality.body) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h9

theorem evaluation10 : @TruthCore.Latin.Aquinas.SummaTheologiae.CompositePosteriorToComponentsReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.component) (TruthCore.Causality.NecessarySimplePlurality.component) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h10

theorem evaluation11 : @TruthCore.Latin.Aquinas.SummaTheologiae.CompositeHasComponentOtherThanItselfReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.composite) (TruthCore.Causality.NecessarySimplePlurality.component) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h11

theorem evaluation12 : @TruthCore.Latin.Aquinas.SummaTheologiae.MatterFormAndEsseEssenceAreCompositionsReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.matterForm) (TruthCore.Causality.NecessarySimplePlurality.composite) (TruthCore.Causality.NecessarySimplePlurality.essence) (TruthCore.Causality.NecessarySimplePlurality.esse) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h12

theorem evaluation13 : @TruthCore.Latin.Aquinas.SummaTheologiae.FirstUnmovedMoverIsSimpleReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves) (TruthCore.Causality.NecessarySimplePlurality.body) (TruthCore.Causality.NecessarySimplePlurality.matterForm) (TruthCore.Causality.NecessarySimplePlurality.composite) (TruthCore.Causality.NecessarySimplePlurality.essence) (TruthCore.Causality.NecessarySimplePlurality.esse) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h13

theorem evaluation14 : @TruthCore.Case.Catholicism.FirstUnmovedMoverIsPureAct (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves) (TruthCore.Models.NecessarySimplePlurality.pureAct) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h14

theorem evaluation15 : @TruthCore.Case.Catholicism.FirstUnmovedMoverHasEveryPerfection (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves) (TruthCore.Causality.NecessarySimplePlurality.inAct) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.simplicity with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  exact h15

theorem evaluation16 : ¬ (@TruthCore.Case.Catholicism.AtMostOneFirstUnmovedMover (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves)) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.uniqueness with ⟨h0, h1, h2, h3, h4, h5⟩
  exact h1

theorem evaluation17 : @TruthCore.Latin.Aquinas.SummaTheologiae.IndividuatingBasisIsIncommunicableReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.suppositum) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.uniqueness with ⟨h0, h1, h2, h3, h4, h5⟩
  exact h2

theorem evaluation18 : @TruthCore.Latin.Aquinas.SummaTheologiae.GodSuppositumIsNatureReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.root) (TruthCore.Causality.NecessarySimplePlurality.suppositum) (TruthCore.Causality.NecessarySimplePlurality.essence) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.uniqueness with ⟨h0, h1, h2, h3, h4, h5⟩
  exact h3

theorem evaluation19 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.ProperGodInstancesHaveCommonNatureReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.root) (TruthCore.Causality.NecessarySimplePlurality.essence) (TruthCore.Causality.NecessarySimplePlurality.Being.left)) := by
  exact (TruthCore.Results.Causality.NecessarySimplePlurality.uniqueness.2.2.2.2.1) Being.left

theorem evaluation20 : ¬ (@TruthCore.Latin.Aquinas.SummaTheologiae.PluralFirstMoversWouldDifferInActReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.moved) (TruthCore.Causality.NecessarySimplePlurality.moves) (TruthCore.Causality.NecessarySimplePlurality.inAct)) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.uniqueness with ⟨h0, h1, h2, h3, h4, h5⟩
  exact h5

theorem evaluation21 : @TruthCore.Explanation.ExistencePSR.Sound (Bool) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.explanation) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.ontology with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  exact h10

theorem evaluation22 : @TruthCore.Explanation.ExistencePSR.ExistencePSR (Bool) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.explanation) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.ontology with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  exact h11

theorem evaluation23 : @TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.DistinctEsseCauseDichotomyReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.esseProfile) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.ontology with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  exact h16

theorem evaluation24 : @TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article4.EssentialPrinciplesCannotCauseDistinctEsseReading (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Being) (TruthCore.Causality.NecessarySimplePlurality.Respect) (TruthCore.Causality.NecessarySimplePlurality.esseProfile) := by
  rcases TruthCore.Results.Causality.NecessarySimplePlurality.ontology with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
  exact h17

theorem evaluation25 : @TruthCore.German.Kant.CosmologicalInference.NecessaryAt
    Bool Being ontic false Being.left :=
  TruthCore.Results.Causality.NecessarySimplePlurality.ontology.2.2.1

theorem evaluation26 : @TruthCore.German.Kant.CosmologicalInference.NecessaryBeing
    Bool Being ontic false :=
  ⟨Being.left, TruthCore.Results.Causality.NecessarySimplePlurality.ontology.2.1 false Being.left,
    TruthCore.Results.Causality.NecessarySimplePlurality.ontology.2.2.1⟩

end TruthCore.Models.NecessarySimplePlurality
