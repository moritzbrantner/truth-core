import TruthCore.Greek.Aristotle.Physics.BookII.Chapter9

namespace TruthCore.Results.Aristotle.Physics.SawHypotheticalNecessity

open TruthCore.Greek.Aristotle.Physics

/-- The saw's stipulated function makes iron hypothetically necessary. -/
theorem sawIronHypotheticallyNecessary
    (SawExists SawHasCuttingFunction SawIsIron : Prop)
    (hSaw : SawHasDeterminateCuttingEndReading SawExists SawHasCuttingFunction)
    (hRequirement : SawFunctionRequiresIronReading SawHasCuttingFunction SawIsIron) :
    SawIronHypotheticallyNecessaryReading SawIsIron := by
  exact hRequirement hSaw.2

end TruthCore.Results.Aristotle.Physics.SawHypotheticalNecessity
