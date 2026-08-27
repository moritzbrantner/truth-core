import TruthCore.Greek.Aristotle.Physics.BookI.Chapter7

namespace TruthCore.Greek.Aristotle.Physics

/-- Attributed dilemma in *Physics* I.8, 191a24-33: any generation must be from being or non-being. -/
def PredecessorGenerationSourceDilemmaReading
    (GenerationOccurs FromBeing FromNotBeing : Prop) : Prop :=
  GenerationOccurs → FromBeing ∨ FromNotBeing

/-- First attributed exclusion in *Physics* I.8, 191a24-33: what already is cannot come to be qua being. -/
def PredecessorRejectsGenerationFromBeingReading (GenerationFromBeing : Prop) : Prop :=
  ¬ GenerationFromBeing

/-- Second attributed exclusion in *Physics* I.8, 191a24-33: nothing comes from sheer non-being. -/
def PredecessorRejectsGenerationFromNotBeingReading (GenerationFromNotBeing : Prop) : Prop :=
  ¬ GenerationFromNotBeing

/-- Attributed conclusion in *Physics* I.8, 191a24-33: the preceding dilemma eliminates generation. -/
def PredecessorDeniesGenerationReading (GenerationOccurs : Prop) : Prop :=
  ¬ GenerationOccurs

/--
Aristotle's first response in *Physics* I.8, 191a34-191b10: expressions about acting,
undergoing, or coming to be from being or non-being must distinguish the respect in which
the description applies, as a doctor builds not qua doctor but qua builder.
-/
def GenerationExpressionsRequireQuaDistinctionReading
    (BeingExpressionsHaveQualifiedSenses QuaRespectMustBeSpecified : Prop) : Prop :=
  BeingExpressionsHaveQualifiedSenses ∧ QuaRespectMustBeSpecified

/--
Qualified non-being solution in *Physics* I.8, 191b13-17: nothing comes without qualification
from non-being, but something can come incidentally from privation, which is non-being in its
own respect and does not persist in the result.
-/
def QualifiedGenerationFromPrivationReading
    (UnqualifiedGenerationFromNotBeing QualifiedGenerationFromPrivation
      PrivationPersistsInResult : Prop) : Prop :=
  ¬ UnqualifiedGenerationFromNotBeing ∧ QualifiedGenerationFromPrivation ∧
    ¬ PrivationPersistsInResult

/--
Parallel being solution in *Physics* I.8, 191b17-26: nothing comes to be from being qua being,
but generation from something that already is can be described incidentally or in a qualified
respect.
-/
def QualifiedGenerationFromBeingReading
    (UnqualifiedGenerationFromBeing QualifiedGenerationFromBeing : Prop) : Prop :=
  ¬ UnqualifiedGenerationFromBeing ∧ QualifiedGenerationFromBeing

/-- Second solution in *Physics* I.8, 191b27-30: the same things can also be explained through potentiality and actuality. -/
def PotentialityActualitySolvesGenerationPuzzleReading
    (PotentialityActualityProvidesSolution : Prop) : Prop :=
  PotentialityActualityProvidesSolution

/-- Closing assessment in *Physics* I.8, 191b30-34: these distinctions dissolve the puzzles that led predecessors to deny generation, destruction, and change. -/
def GenerationPuzzlesResolvedReading (GenerationPuzzlesResolved : Prop) : Prop :=
  GenerationPuzzlesResolved

end TruthCore.Greek.Aristotle.Physics
