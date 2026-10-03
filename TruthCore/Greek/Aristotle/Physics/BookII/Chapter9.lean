import TruthCore.Greek.Aristotle.Physics.BookII.Chapter8

namespace TruthCore.Greek.Aristotle.Physics

/--
Opening question and attributed view in Aristotle, *Physics* II.9, 199b34-200a5: necessity
in nature may be hypothetical or simple, while the current view treats material tendencies
as sufficient to necessitate production, as though weight and lightness alone explained the
construction of a wall.

Source: Aristotle, *Physics* II.9, 199b34-200a5 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def AttributedMaterialSequenceSufficesForProductionReading
    (NaturalNecessityMayBeHypotheticalOrSimple
      CurrentViewMakesMaterialTendenciesSufficient
      WeightAndLightnessAloneExplainWall : Prop) : Prop :=
  NaturalNecessityMayBeHypotheticalOrSimple ∧
    CurrentViewMakesMaterialTendenciesSufficient ∧
      WeightAndLightnessAloneExplainWall

/--
Wall reply in Aristotle, *Physics* II.9, 200a5-8: a wall cannot arise without its materials,
but it does not arise because of them except as matter; it arises for shelter and protection.

Source: Aristotle, *Physics* II.9, 200a5-8 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def WallNeedsMatterButExistsForShelterReading
    (WallCannotExistWithoutMaterials
      MaterialsCauseWallAsMatter
      MaterialsAreSufficientWhyForWall
      WallExistsForShelterAndProtection : Prop) : Prop :=
  WallCannotExistWithoutMaterials ∧
    MaterialsCauseWallAsMatter ∧
      ¬ MaterialsAreSufficientWhyForWall ∧
        WallExistsForShelterAndProtection

/--
Saw-case premise in Aristotle, *Physics* II.9, 200a8-13: the saw exists with a determinate
cutting function and for the sake of that operation.

Source: Aristotle, *Physics* II.9, 200a8-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SawHasDeterminateCuttingEndReading
    (SawExists SawHasCuttingFunction : Prop) : Prop :=
  SawExists ∧ SawHasCuttingFunction

/--
Material-requirement bridge in Aristotle, *Physics* II.9, 200a8-13: realizing the saw's
cutting function requires that the saw be iron.

Source: Aristotle, *Physics* II.9, 200a8-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SawFunctionRequiresIronReading
    (SawHasCuttingFunction SawIsIron : Prop) : Prop :=
  SawHasCuttingFunction → SawIsIron

/--
Conclusion of the saw example in Aristotle, *Physics* II.9, 200a8-13: given the saw and its
function, its being iron is necessary.

Source: Aristotle, *Physics* II.9, 200a8-13 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def SawIronHypotheticallyNecessaryReading (SawIsIron : Prop) : Prop :=
  SawIsIron

/--
Central distinction in Aristotle, *Physics* II.9, 200a13-15: natural necessity is
hypothetical rather than the end; necessity belongs in matter, while the for-the-sake-of
belongs in the account or definition.

Source: Aristotle, *Physics* II.9, 200a13-15 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def HypotheticalNecessityMatterEndAccountReading
    (NaturalNecessityIsHypothetical
      NecessityIsFinalCause
      NecessityBelongsInMatter
      EndBelongsInAccount : Prop) : Prop :=
  NaturalNecessityIsHypothetical ∧
    ¬ NecessityIsFinalCause ∧
      NecessityBelongsInMatter ∧
        EndBelongsInAccount

/--
Mathematical analogy and reversal in Aristotle, *Physics* II.9, 200a15-22: mathematical
necessity follows from what a thing is, while in end-directed generation the existence of the
end requires the preceding conditions. The end is a principle of reasoning, not of action.

Source: Aristotle, *Physics* II.9, 200a15-22 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def MathematicalNaturalNecessityDirectionReading
    (MathematicalConsequenceFollowsFromEssence
      EndDirectedGenerationRequiresPrecedingConditions
      EndIsPrincipleOfReasoning
      EndIsPrincipleOfAction : Prop) : Prop :=
  MathematicalConsequenceFollowsFromEssence ∧
    EndDirectedGenerationRequiresPrecedingConditions ∧
      EndIsPrincipleOfReasoning ∧
        ¬ EndIsPrincipleOfAction

/--
Material-condition summary in Aristotle, *Physics* II.9, 200a22-30: a house requires bricks
and stones and a saw requires iron, but neither end exists because of those materials except
in the material-cause sense; without them the end cannot exist.

Source: Aristotle, *Physics* II.9, 200a22-30 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def EndRequiresMatterWithoutBeingCausedByItReading
    (HouseRequiresBricksAndStones
      SawRequiresIron
      EndsExistBecauseOfMatterAsFinalCause
      EndsCannotExistWithoutRequiredMatter : Prop) : Prop :=
  HouseRequiresBricksAndStones ∧
    SawRequiresIron ∧
      ¬ EndsExistBecauseOfMatterAsFinalCause ∧
        EndsCannotExistWithoutRequiredMatter

/--
Physical explanatory priority in Aristotle, *Physics* II.9, 200a30-33: necessity in nature
is matter and its motions. The physicist must state both material and final causes, but
especially the end, because the end explains the matter rather than matter explaining the end.

Source: Aristotle, *Physics* II.9, 200a30-33 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def PhysicistStatesMatterAndEndWithEndPriorityReading
    (NaturalNecessityIsMatterAndItsMotions
      PhysicistMustStateMaterialCause
      PhysicistMustStateFinalCause
      EndExplainsMatter
      MatterExplainsEnd : Prop) : Prop :=
  NaturalNecessityIsMatterAndItsMotions ∧
    PhysicistMustStateMaterialCause ∧
      PhysicistMustStateFinalCause ∧
        EndExplainsMatter ∧
          ¬ MatterExplainsEnd

/--
Definitional necessity in Aristotle, *Physics* II.9, 200a33-200b9: definitions of house,
health, human being, or sawing determine necessary preceding conditions and materials; some
parts of an account function as matter of the account.

Source: Aristotle, *Physics* II.9, 200a33-200b9 (Bekker pagination).
CTS work: `urn:cts:greekLit:tlg0086.tlg031`.
-/
def DefinitionDeterminesNecessaryConditionsReading
    (EssenceDeterminesNecessaryPreconditions
      SawingDefinitionRequiresSuitableTeeth
      SuitableSawTeethRequireIron
      SomeAccountPartsServeAsMatterOfAccount : Prop) : Prop :=
  EssenceDeterminesNecessaryPreconditions ∧
    SawingDefinitionRequiresSuitableTeeth ∧
      SuitableSawTeethRequireIron ∧
        SomeAccountPartsServeAsMatterOfAccount

end TruthCore.Greek.Aristotle.Physics
