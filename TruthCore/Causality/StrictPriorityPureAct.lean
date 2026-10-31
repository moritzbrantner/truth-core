import TruthCore.Causality.NecessaryFirstBeing
import TruthCore.Causality.DirectEsseGenusOmissionControl
import Mathlib.Order.Defs.Unbundled

/-! Alternative conditional no-potency route and two finite separation controls.
No source attribution or metaphysical applicability is asserted. -/
namespace TruthCore.Causality.StrictPriorityPureAct
open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.WholeRosterFoundation
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

/-- OPEN: this very simple-priority relation is irreflexive. This is the standard
Mathlib/Lean relation property, not irreflexivity of mixed act/bearer priority.
It imposes no transitivity, well-foundedness or temporal interpretation. -/
def StrictSimplePriority {B : Type} (PriorSimply : B → B → Prop) : Prop :=
  Std.Irrefl PriorSimply

namespace Controls
open TruthCore.Causality.NecessarySimplePlurality
abbrev model := TruthCore.Causality.DirectEsseGenusOmissionControl.profile
/-- Only priority is varied: add a self-loop at the nonroot instrument. -/
def loopPriority (y x : Being) : Prop :=
  component y x ∨ (y = x ∧ x = Being.instrument)
/-- A separately varied act assignment; potency and all ontic fields stay fixed. -/
def allAct (_ : Being) (_ : Respect) : Prop := True
/-- Five nonlogical inputs common to both seven-input packages. EM is explicit
in the registered control theorem, hence six unchanged inputs in each package. -/
def Common (Prior : Being → Being → Prop) (Act : Being → Respect → Prop) : Prop :=
  InhabitedConcreteAt model.ontic model.concrete false ∧
  WholeRosterNotTrapped model false ∧ EveryContingentGroundedAt model false ∧
  SimplyPriorIsActualConcreteGround model false Prior ∧
  ActSimplyPriorToPotencyReading Act moved Prior
/-- Two assignments on the SAME old carrier/profile. One retains exclusivity
but fails strictness; the other retains strictness but fails exclusivity.
These are formal separation controls, not metaphysically possible worlds. -/
def Separation : Prop :=
  Common loopPriority inAct ∧ NotActAndPotencyInSameRespectReading inAct moved ∧
  ¬ StrictSimplePriority loopPriority ∧
  Common component allAct ∧ StrictSimplePriority component ∧
  ¬ NotActAndPotencyInSameRespectReading allAct moved
end Controls
end TruthCore.Causality.StrictPriorityPureAct
