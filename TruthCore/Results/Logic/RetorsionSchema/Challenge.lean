import TruthCore.Alternatives.FirstClosure
import TruthCore.Alternatives.Retorsion

namespace TruthCore.Results.Logic.RetorsionSchema
open TruthCore.Logic.Retorsion
open TruthCore.Alternatives.Retorsion

/-- The retorsion schema: given the presupposition link, the held position of
any typed global underminer is inconsistent. -/
theorem retorsionSchema : RetorsionSchema := by
  sorry

/-- Control: without the link, a held underminer position is consistent. -/
theorem linkNeeded : ∃ U : Underminer Unit Unit, U.Position := by
  sorry

/-- Control: without holding, the link and the thesis are consistent. -/
theorem heldNeeded :
    ∃ (U : Underminer Unit Unit) (trace : Unit → Prop → Unit), U.Link trace ∧ U.thesis := by
  sorry

/-- The Eleatic retorsion (*Physics* VIII.3, 254a27-30) as a schema instance. -/
theorem eleaticRetorsionInstance : EleaticRetorsionInstance := by
  sorry

/-- McTaggart's § 511 answer escapes the schema at the presupposition link. -/
theorem mcTaggartEscapesRetorsion : McTaggartEscapesRetorsion := by
  sorry

end TruthCore.Results.Logic.RetorsionSchema
