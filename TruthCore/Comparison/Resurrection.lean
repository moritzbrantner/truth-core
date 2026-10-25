import TruthCore.History.Resurrection

/-! Theories for the stage-4 pilot. These are expressly limited bundles of
propositions, not new corpus entities. Their common findings are accepted
open premises. Counts describe this encoding; they do not rank worldviews. -/
namespace TruthCore.Comparison.Resurrection
open TruthCore.History.Resurrection

def Catholic (s : State) : Prop :=
  Crucifixion s ∧ EarlyProclamation s ∧ TombTradition s ∧
  SincereExperiences s ∧ PaulConversion s ∧ JamesConversion s ∧
  GodExists s ∧ DivineCause s ∧ JesusClaims s ∧ AuthorityVindicated s ∧
  Rose s ∧ CatholicAccount s

def Legend (s : State) : Prop :=
  Crucifixion s ∧ EarlyProclamation s ∧ TombTradition s ∧
  SincereExperiences s ∧ PaulConversion s ∧ JamesConversion s ∧ LegendAccount s

def Hallucination (s : State) : Prop :=
  Crucifixion s ∧ EarlyProclamation s ∧ TombTradition s ∧
  SincereExperiences s ∧ PaulConversion s ∧ JamesConversion s ∧ VisionAccount s

def GroupHallucination (s : State) : Prop :=
  Crucifixion s ∧ EarlyProclamation s ∧ TombTradition s ∧
  SincereExperiences s ∧ PaulConversion s ∧ JamesConversion s ∧ GroupAccount s

def StolenBody (s : State) : Prop :=
  Crucifixion s ∧ EarlyProclamation s ∧ TombTradition s ∧
  SincereExperiences s ∧ PaulConversion s ∧ JamesConversion s ∧ TheftAccount s

def Swoon (s : State) : Prop :=
  Crucifixion s ∧ EarlyProclamation s ∧ TombTradition s ∧
  SincereExperiences s ∧ PaulConversion s ∧ JamesConversion s ∧ SwoonAccount s

def CatholicConsistent : Prop := ∃ s, Catholic s
def LegendConsistent : Prop := ∃ s, Legend s
def HallucinationConsistent : Prop := ∃ s, Hallucination s
def GroupHallucinationConsistent : Prop := ∃ s, GroupHallucination s
def StolenBodyConsistent : Prop := ∃ s, StolenBody s
def SwoonConsistent : Prop := ∃ s, Swoon s
end TruthCore.Comparison.Resurrection
