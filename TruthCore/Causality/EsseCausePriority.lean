module

public import TruthCore.Causality.Round2Grounding
public import TruthCore.Causality.CreatureSenses
public import TruthCore.Case.Catholicism.CauseOfBeingHasBeing
public import TruthCore.Causality.ActPriorityAtFirst
public import TruthCore.Causality.ComponentFirstness

/-! Esse-cause priority through actual grounding, without modal separability (#1604)

Analyst formulations, attribution deferred. The root route's only registered
derivation of `STMT-EFFICIENT-CAUSE-IS-PRIOR-TO-EFFECT` runs through
`STMT-NONMUTUAL-DEPENDENCE-SUFFICES-FOR-PRIORITY`, whose only derivation takes
the modal separability premise `STMT-INDEPENDENCE-ALLOWS-BEING-WITHOUT`
(see `docs/notes/god-existence-support-formula.md`). This module gives a
sibling path to priority for a **distinct cause of esse**, through the profile's
selected grounding relation, using neither `DependsForBeing` nor any
possible-separation premise:

* `ActualEsseCausePriority`: a distinct cause of the esse of an actual
  concretum at `w` is simply prior to it. It is the composition of the two
  existing OPEN bridges `EsseCauseIsActualConcreteGround` (causing the esse of
  an actual concretum is being its actual concrete ground) and
  `ActualGroundingIsSimplePriority` (actual grounding is simple priority).
* `DistinctEsseCausePriority`: the same with no actuality antecedent. The
  existing consumers of efficient-cause priority on the stage-two routes
  (`noComponentFirst`, `firstBeingNoPotencyOfComposition` and their weak
  versions) apply it only to a distinct cause of the esse of a supposed first
  being, with no profile and no actuality hypothesis. Three existing OPEN
  statements supply that antecedent: a caused esse is had
  (`CreatureSenses.CausedEsseIsHad`), what is in act of esse exists at `w`
  (`Round2ExistenceAct.ActOfEsseSufficesForExistenceAt`) and what has esse in
  re is concrete in the profile (`CauseOfBeingHasBeing.EsseInReIsConcrete`).

`CausesIn` is the one shared cause-of-perfection relation (DEF-CAUSE-OF-
PERFECTION) at `esse`, the relation of the q.3 a.7 cause premise; no premise
passes to efficient causing. `PriorSimply` is the primitive SIMPLY_PRIOR_1.
`DistinctEsseCausePriority` is strictly weaker than
`EfficientCauseIsPriorToEffectReading` read on the same relation: it says
nothing about self-causes or about respects other than esse
(`Control.NotEfficientPriority`). It therefore cannot serve the consumers that
need those instances (no self-cause, causal well-foundedness, the secunda via).
-/

@[expose] public section

namespace TruthCore.Causality.EsseCausePriority

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)

variable {W B R : Type}

/-- A distinct cause of the esse of an actual concretum at `w` is simply prior
to it. Scoped to actual concreta at one world and to the respect `esse`. -/
def ActualEsseCausePriority (m : Profile W B) (w : W) (CausesIn : B → B → R → Prop)
    (esse : R) (PriorSimply : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → ActualConcrete m w x → CausesIn c x esse → PriorSimply c x

/-- A distinct cause of a thing's esse is simply prior to it. No self-cause and
no respect other than esse is covered. -/
def DistinctEsseCausePriority (CausesIn : B → B → R → Prop) (esse : R)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → CausesIn c x esse → PriorSimply c x

/-! ## Controls

Finite interpretations with `Bool` worlds, beings and respects (the reading
world and `esse` are `true`), built with `Round2Grounding.Control.mk`.
Satisfiability and omission only; no model is claimed to describe reality. -/

namespace Control

open TruthCore.Causality.NecessaryConcreteRouteBridge (EsseCauseIsActualConcreteGround)
open TruthCore.Causality.Round2Grounding (ActualGroundingIsSimplePriority)
open TruthCore.Causality.CreatureSenses (CausedEsseIsHad)
open TruthCore.Causality.Round2ExistenceAct (ActOfEsseSufficesForExistenceAt)
open TruthCore.Case.Catholicism.CauseOfBeingHasBeing (EsseInReIsConcrete)
open TruthCore.Latin.Aquinas.SummaTheologiae (EfficientCauseIsPriorToEffectReading)

/-- Everything exists everywhere and is concrete; nothing is grounded. -/
abbrev bare : Profile Bool Bool :=
  Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => True) (fun _ => True)
    (fun _ _ _ => False) (fun _ _ _ => False)
/-- As `bare`, but `true` grounds `false` at `true`. -/
abbrev grounded : Profile Bool Bool :=
  Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => True) (fun _ => True)
    (fun _ _ _ => False) (fun w g x => w = true ∧ g = true ∧ x = false)
/-- `true` causes the esse of `false`. -/
abbrev causes (c x r : Bool) : Prop := c = true ∧ x = false ∧ r = true
/-- `true` is simply prior to `false`. -/
abbrev prior (y x : Bool) : Prop := y = true ∧ x = false
/-- Nothing is simply prior to anything. -/
abbrev noPrior (_ _ : Bool) : Prop := False
/-- Everything is in act in every respect. -/
abbrev allAct (_ _ : Bool) : Prop := True

/-- Joint witness: both bridges hold with a nonvacuous instance (an actual
concretum `false` whose esse `true` causes), and the conclusion's instance holds. -/
def Witness : Prop :=
  EsseCauseIsActualConcreteGround grounded true causes true ∧
  ActualGroundingIsSimplePriority grounded true prior ∧
  ActualConcrete grounded true false ∧ causes true false true ∧ prior true false

/-- Omitting the esse-cause bridge: actual grounding is simple priority (vacuously:
nothing grounds), an actual concretum has a distinct esse cause, and the
scoped priority fails. -/
def OmitEsseGround : Prop :=
  ActualGroundingIsSimplePriority bare true noPrior ∧
  ¬ ActualEsseCausePriority bare true causes true noPrior

/-- Omitting the grounding-to-priority bridge: the esse cause grounds its actual
effect, nothing is simply prior, and the scoped priority fails. -/
def OmitGroundingPriority : Prop :=
  EsseCauseIsActualConcreteGround grounded true causes true ∧
  ¬ ActualEsseCausePriority grounded true causes true noPrior

/-- The three antecedent-supplying bridges and both priority bridges hold jointly
with a nonvacuous esse cause. -/
def ScopeWitness : Prop :=
  CausedEsseIsHad causes allAct true ∧
  ActOfEsseSufficesForExistenceAt grounded.ontic allAct true true ∧
  EsseInReIsConcrete grounded allAct true ∧
  EsseCauseIsActualConcreteGround grounded true causes true ∧
  ActualGroundingIsSimplePriority grounded true prior

/-- Omitting `CausedEsseIsHad`: nothing is in act, nothing exists, so the scoped
priority holds vacuously, the other two scope bridges hold, a distinct esse cause
exists, and the unscoped priority fails. -/
def OmitCausedEsseIsHad : Prop :=
  ActualEsseCausePriority
    (Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => False) (fun _ => False)
      (fun _ _ _ => False) (fun _ _ _ => False)) true causes true noPrior ∧
  ActOfEsseSufficesForExistenceAt
    (Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => False) (fun _ => False)
      (fun _ _ _ => False) (fun _ _ _ => False)).ontic (fun _ _ => False) true true ∧
  EsseInReIsConcrete
    (Round2Grounding.Control.mk (fun _ _ => True) (fun _ _ => False) (fun _ => False)
      (fun _ _ _ => False) (fun _ _ _ => False)) (fun _ _ => False) true ∧
  ¬ DistinctEsseCausePriority causes true noPrior

/-- The distinct-esse-cause version does not give efficient-cause priority on
the same relation: `true` causes its own esse and is not prior to itself, while
the distinct-cause version holds vacuously. -/
def NotEfficientPriority : Prop :=
  DistinctEsseCausePriority (fun c x r => c = true ∧ x = true ∧ r = true) true noPrior ∧
  ¬ EfficientCauseIsPriorToEffectReading (fun c x r => c = true ∧ x = true ∧ r = true) noPrior

/-- The controls of this module. -/
def Certificate : Prop :=
  Witness ∧ OmitEsseGround ∧ OmitGroundingPriority ∧ ScopeWitness ∧
  OmitCausedEsseIsHad ∧ NotEfficientPriority

end Control

end TruthCore.Causality.EsseCausePriority
