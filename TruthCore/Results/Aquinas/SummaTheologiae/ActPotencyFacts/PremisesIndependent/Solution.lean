module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.ActPotencyTheory
public import TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyModels

@[expose] public section

namespace TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.PremisesIndependent
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Countermodels: each act/potency premise fails in a finite model of all the others (`ActPotencyModels.M1`–`M8`). No premises. -/
theorem premisesIndependent : ActPotencyPremisesIndependent :=
  ActPotencyModels.premisesIndependent

end TruthCore.Results.Aquinas.SummaTheologiae.ActPotencyFacts.PremisesIndependent
