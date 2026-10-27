import TruthCore.Alternatives.FirstClosure
import TruthCore.Alternatives.Retorsion

namespace TruthCore.Results.Logic.RetorsionSchema
open TruthCore.Logic.Retorsion
open TruthCore.Alternatives.Retorsion
open TruthCore.Alternatives.ActPotencyRegress
open TruthCore.Alternatives.McTaggart

/-- The retorsion schema: given the presupposition link, the held position of
any typed global underminer is inconsistent. -/
theorem retorsionSchema : RetorsionSchema :=
  fun _ _ U _ hLink => U.position_inconsistent hLink

/-- Control: without the link, a held underminer position is consistent. -/
theorem linkNeeded : ∃ U : Underminer Unit Unit, U.Position :=
  ⟨{ Performs := fun _ _ => True, Feature := fun _ => False,
     thesis := True, denies := fun _ _ h => h }, trivial, (), trivial⟩

/-- Control: without holding, the link and the thesis are consistent. -/
theorem heldNeeded :
    ∃ (U : Underminer Unit Unit) (trace : Unit → Prop → Unit), U.Link trace ∧ U.thesis :=
  ⟨{ Performs := fun _ _ => False, Feature := fun _ => False,
     thesis := True, denies := fun _ _ h => h }, fun _ _ => (), fun _ _ h => h, trivial⟩

/-- The Eleatic retorsion (*Physics* VIII.3, 254a27-30) as a schema instance. -/
theorem eleaticRetorsionInstance : EleaticRetorsionInstance :=
  fun _ _ _ _ _ hOpinionIsMotion hHeld => eleaticThesisFalse_of_schema hOpinionIsMotion hHeld

/-- McTaggart's § 511 answer escapes the schema at the presupposition link. -/
theorem mcTaggartEscapesRetorsion : McTaggartEscapesRetorsion := by
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ _ hReply hLink
    obtain ⟨⟨x, p, hx⟩, hNo⟩ := hReply
    exact hNo x p hx (hLink x p hx)
  · intro _ _ _ _ _ _ hReply hBridge hLink
    exact appearingsDoNotChange_denies_opinionIsMotion hReply hBridge hLink
  · obtain ⟨hHeld, hBridge, hNoA, hAll, hNothing, -, -, -⟩ :=
      TruthCore.Alternatives.FirstClosure.opinionGate
    have hReply : AppearingsDoNotChangeReading (fun (_ : Unit) (_ : Prop) => True)
        (fun _ => False) := ⟨⟨(), True, trivial⟩, fun _ _ _ h => h⟩
    refine ⟨_, _, _, _, ⟨hNoA, hAll⟩, hReply, hBridge,
      ⟨fun _ h => h, (), trivial⟩, ⟨hNothing, hHeld⟩, ?_, ?_⟩
    · intro hLink
      exact hReply.2 () True trivial (hLink () True trivial)
    · intro asOpinion hLink
      exact appearingsDoNotChange_denies_opinionIsMotion (asOpinion := asOpinion) hReply hBridge hLink

end TruthCore.Results.Logic.RetorsionSchema
