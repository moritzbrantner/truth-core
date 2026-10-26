import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPotencyTheory
import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels
namespace TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.BeingInActReading
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Facts about the being-in-act reading of *nisi per aliquod ens in actu*: two entailments and two countermodels (`ActPotencyModels.S1`, `S2`). No premises. -/
theorem beingInActReadingFacts : BeingInActReadingFacts :=
  ActPotencyModels.beingInActReadingFacts

end TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.BeingInActReading
