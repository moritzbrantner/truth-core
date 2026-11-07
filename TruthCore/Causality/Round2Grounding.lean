module

public import TruthCore.Causality.NecessaryConcreteRouteBridge
public import TruthCore.Causality.MaximalGroundingAsymmetry
public import TruthCore.Causality.CausalMapsBatch1
public import TruthCore.Causality.GodMaximalCausal

/-! Round 2 grounding: routes into the actual-concrete-grounding bridges

Analyst formulations, attribution deferred. Six exploration maps
(`explorations/every-contingent-grounded-at.toml`,
`explorations/esse-cause-actual-concrete-ground.toml`,
`explorations/simply-prior-actual-concrete-ground.toml`,
`explorations/necessity-causes-actual-concrete-grounds.toml`,
`explorations/actual-grounding-asymmetric.toml`,
`explorations/actual-grounding-asymmetric-at-maximal-target.toml`) propose
derivations of underived root-path bridges of the necessary-being cluster that
are stated in the `Profile` vocabulary (`BruteFoundationBoundary.Profile`:
world-relative existence `ExistsAt`, the `concrete` predicate and the selected
relation `grounds w y x`, read as "`y` grounds `x` at `w`"). Every new
proposition below is an OPEN premise: an analyst bridge, or a reading recorded
as `supported` by an existing claim with its gap. None is attributed as stated.

Vocabulary reused exactly: `CausesIn` and `MoreIn` (DEF-CAUSE-OF-PERFECTION,
DEF-MORE-IN), `PriorSimply` (DEF-SIMPLE-PRIORITY), `DependsForBeing`
(DEF-DEPENDS-FOR-BEING, from `CausalMapsBatch1`), the tertia via's
`CausesNecessityOf` (DEF-NECESSARY-PER-SE), Kant's `Ontic.Causes`
(DEF-KANT-LOCAL-CAUSE) and `ContingentAt` (DEF-KANT-MODAL-CONTINGENCY). One new
primitive parameter:

* `Participates x` (DEF-PARTICIPATED-ESSE): `x` has esse by participation,
  that is, `x` is not its own esse but has it as received (ST I q.44 a.1 co.).
  It is a parameter; nothing here identifies it with contingency, which is the
  open premise `ContingentConcretumParticipatesEsse`.

The bridges relate distinct relations (causing esse, dependence for being,
simple priority, Kant's local cause, grades of esse) to the selected `grounds`
relation. They do not identify any of them with it (DISAMB-CAUSE,
DISAMB-CAUSAL-POWER-GROUNDING): each is a one-directional open premise. -/

@[expose] public section

namespace TruthCore.Causality.Round2Grounding

open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Causality.NecessaryRootFork (ActualConcrete)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt)

variable {W B R : Type}

/-! ## Causes of esse -/

/-- Whatever causes the esse of an actual concretum exists at the reading world.
Supported by CC100 #10's "only actually existing things can be causes". -/
def EsseCausesExistAt (m : Profile W B) (w : W) (CausesIn : B → B → R → Prop)
    (esse : R) : Prop :=
  ∀ c x, ActualConcrete m w x → CausesIn c x esse → m.ontic.ExistsAt w c

/-- Whatever causes the esse of something is concrete (concreteness read as
causal capacity, as in CC100 #11's gloss of "concrete"). -/
def EsseCausesAreConcrete (m : Profile W B) (CausesIn : B → B → R → Prop)
    (esse : R) : Prop :=
  ∀ c x, CausesIn c x esse → m.concrete c

/-- A thing whose esse is caused by another depends for its being on that other
(ST I q.44 a.1 ad 2 read for causes of esse). -/
def EsseEffectDependsOnItsCause (CausesIn : B → B → R → Prop) (esse : R)
    (DependsForBeing : B → B → Prop) : Prop :=
  ∀ c x, c ≠ x → CausesIn c x esse → DependsForBeing x c

/-- Dependence for being between actual concreta is the selected grounding:
if actual concrete `x` depends for its being on actual concrete `c`, then `c`
grounds `x` at `w`. One direction only; grounding is not claimed to be
dependence. -/
def ActualDependenceIsGrounding (m : Profile W B) (w : W)
    (DependsForBeing : B → B → Prop) : Prop :=
  ∀ c x, ActualConcrete m w x → ActualConcrete m w c → DependsForBeing x c → m.grounds w c x

/-! ## Simple priority and causes of necessity -/

/-- Both relata of simple priority are actual concreta at `w`. -/
def SimplePriorityRelatesActualConcreta (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ y x, PriorSimply y x → ActualConcrete m w y ∧ ActualConcrete m w x

/-- Whatever causes the necessity of a thing causes its esse (the converse
direction of `CauseOfNecessaryBeingCausesItsNecessity`). -/
def NecessityCauseCausesEsse (CausesNecessityOf : B → B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ c x, CausesNecessityOf c x → CausesIn c x esse

/-- Both relata of causing necessity are actual concreta at `w`. -/
def NecessityCauseRelataActualConcrete (m : Profile W B) (w : W)
    (CausesNecessityOf : B → B → Prop) : Prop :=
  ∀ c x, CausesNecessityOf c x → ActualConcrete m w c ∧ ActualConcrete m w x

/-- A thing whose necessity is caused depends for its being on the cause of its
necessity. -/
def NecessitatedDependsOnItsCause (CausesNecessityOf : B → B → Prop)
    (DependsForBeing : B → B → Prop) : Prop :=
  ∀ c x, CausesNecessityOf c x → DependsForBeing x c

/-! ## Contingent concreta -/

/-- Every actual contingent concretum has esse by participation. -/
def ContingentConcretumParticipatesEsse (m : Profile W B) (w : W)
    (Participates : B → Prop) : Prop :=
  ∀ x, ActualConcrete m w x → ContingentAt m.ontic w x → Participates x

/-- Whatever has esse by participation has its esse caused by something other
than itself (reading of ST I q.44 a.1 co.). -/
def ParticipatedEsseHasDistinctCause (Participates : B → Prop)
    (CausesIn : B → B → R → Prop) (esse : R) : Prop :=
  ∀ x, Participates x → ∃ c, c ≠ x ∧ CausesIn c x esse

/-- Every actual contingent concretum depends for its being on some actual
concretum. -/
def ActualContingentDependsOnActualConcretum (m : Profile W B) (w : W)
    (DependsForBeing : B → B → Prop) : Prop :=
  ∀ x, ActualConcrete m w x → ContingentAt m.ontic w x →
    ∃ y, ActualConcrete m w y ∧ DependsForBeing x y

/-- An existing Kantian cause (`Ontic.Causes`) of an actual concretum is
concrete and grounds it at `w`. -/
def ExistingCauseOfActualConcretumIsConcreteGround (m : Profile W B) (w : W) : Prop :=
  ∀ y x, ActualConcrete m w x → m.ontic.ExistsAt w y → m.ontic.Causes w y x →
    m.concrete y ∧ m.grounds w y x

/-! ## Asymmetry -/

/-- Grounding between actual concreta is simple priority of the ground. -/
def ActualGroundingIsSimplePriority (m : Profile W B) (w : W)
    (PriorSimply : B → B → Prop) : Prop :=
  ∀ a b, ActualConcrete m w a → ActualConcrete m w b → m.grounds w a b → PriorSimply a b

/-- Grounding between actual concreta is dependence of the grounded on its
ground. -/
def ActualGroundingIsDependence (m : Profile W B) (w : W)
    (DependsForBeing : B → B → Prop) : Prop :=
  ∀ a b, ActualConcrete m w a → ActualConcrete m w b → m.grounds w a b → DependsForBeing b a

/-- Dependence for being is asymmetric (hence irreflexive). -/
def DependenceForBeingAsymmetric (DependsForBeing : B → B → Prop) : Prop :=
  ∀ x y, DependsForBeing x y → ¬ DependsForBeing y x

/-- An actual concrete ground is more in esse than the actual concretum it
grounds. -/
def ActualGroundIsMoreInEsse (m : Profile W B) (w : W) (MoreIn : R → B → B → Prop)
    (esse : R) : Prop :=
  ∀ a b, ActualConcrete m w a → ActualConcrete m w b → m.grounds w a b → MoreIn esse a b

/-! ## Controls

Finite interpretations on `Bool` carriers (worlds, beings and respects; the
reading world and `esse` are `true`), checked by `decide` after unfolding, so
that no axiom is used. In two-world models, `false` exists only at world `true`
and is therefore contingent there. Satisfiability and omission only; no model
is claimed to describe reality. -/

namespace Control

open TruthCore.Causality.CogitoNecessaryConcrete (ActualConcreteGround)
open TruthCore.Causality.NecessaryRootFork (ActualGroundingWF)
open TruthCore.Causality.BruteFoundationBoundary (EveryContingentGroundedAt)
open TruthCore.Causality.NecessaryConcreteRouteBridge
open TruthCore.Causality.MaximalGroundingAsymmetry (AtMaximalTarget)
open TruthCore.Causality.CausalMapsBatch1 (PriorityRequiresNonmutualDependence)
open TruthCore.Causality.GodMaximalCausal (MoreInIsAsymmetric)
open TruthCore.Case.Catholicism (SimplyPriorIsCauseOfBeing)
open TruthCore.German.Kant.CosmologicalInference (LocalCausalPrinciple)

/-- A profile on `Bool` worlds and `Bool` beings from its five components. -/
abbrev mk (acc ex : Bool → Bool → Prop) (conc : Bool → Prop)
    (cau gr : Bool → Bool → Bool → Prop) : Profile Bool Bool :=
  { ontic := { frame := { access := acc }, ExistsAt := ex, Causes := cau }
    concrete := conc, grounds := gr }

namespace wf
/-- Omission model for `hWF` of `asymmetricFromWF`: the two actual concreta ground
each other (and themselves). -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => True
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
/-- The omission condition. -/
def Holds : Prop := ¬ ActualGroundingWF m true ∧ ¬ ActualGroundingAsymmetric m true
end wf

namespace esseCauseGroundViaDependence.omit_hGround
/-- Omission model for `hGround` of `esseCauseGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (EsseCausesExistAt m true C true) ∧
    (EsseCausesAreConcrete m C true) ∧
    (EsseEffectDependsOnItsCause C true D) ∧
    ¬ (ActualDependenceIsGrounding m true D) ∧
    ¬ (EsseCauseIsActualConcreteGround m true C true)
end esseCauseGroundViaDependence.omit_hGround

namespace esseCauseGroundViaDependence.omit_hExists
/-- Omission model for `hExists` of `esseCauseGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ b => b = false
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ y x => y = true ∧ x = false
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (EsseCausesExistAt m true C true) ∧
    (EsseCausesAreConcrete m C true) ∧
    (EsseEffectDependsOnItsCause C true D) ∧
    (ActualDependenceIsGrounding m true D) ∧
    ¬ (EsseCauseIsActualConcreteGround m true C true)
end esseCauseGroundViaDependence.omit_hExists

namespace esseCauseGroundViaDependence.omit_hConcrete
/-- Omission model for `hConcrete` of `esseCauseGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun b => b = false
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ y x => y = true ∧ x = false
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (EsseCausesExistAt m true C true) ∧
    ¬ (EsseCausesAreConcrete m C true) ∧
    (EsseEffectDependsOnItsCause C true D) ∧
    (ActualDependenceIsGrounding m true D) ∧
    ¬ (EsseCauseIsActualConcreteGround m true C true)
end esseCauseGroundViaDependence.omit_hConcrete

namespace esseCauseGroundViaDependence.omit_hDep
/-- Omission model for `hDep` of `esseCauseGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (EsseCausesExistAt m true C true) ∧
    (EsseCausesAreConcrete m C true) ∧
    ¬ (EsseEffectDependsOnItsCause C true D) ∧
    (ActualDependenceIsGrounding m true D) ∧
    ¬ (EsseCauseIsActualConcreteGround m true C true)
end esseCauseGroundViaDependence.omit_hDep

namespace simplyPriorGroundViaDependence.omit_hReq
/-- Omission model for `hReq` of `simplyPriorGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (PriorityRequiresNonmutualDependence P D) ∧
    (SimplePriorityRelatesActualConcreta m true P) ∧
    (ActualDependenceIsGrounding m true D) ∧
    ¬ (SimplyPriorIsActualConcreteGround m true P)
end simplyPriorGroundViaDependence.omit_hReq

namespace simplyPriorGroundViaDependence.omit_hRel
/-- Omission model for `hRel` of `simplyPriorGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ b => b = false
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ y x => y = true ∧ x = false
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (PriorityRequiresNonmutualDependence P D) ∧
    ¬ (SimplePriorityRelatesActualConcreta m true P) ∧
    (ActualDependenceIsGrounding m true D) ∧
    ¬ (SimplyPriorIsActualConcreteGround m true P)
end simplyPriorGroundViaDependence.omit_hRel

namespace simplyPriorGroundViaDependence.omit_hGround
/-- Omission model for `hGround` of `simplyPriorGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (PriorityRequiresNonmutualDependence P D) ∧
    (SimplePriorityRelatesActualConcreta m true P) ∧
    ¬ (ActualDependenceIsGrounding m true D) ∧
    ¬ (SimplyPriorIsActualConcreteGround m true P)
end simplyPriorGroundViaDependence.omit_hGround

namespace simplyPriorGroundViaEsseCause.omit_hCause
/-- Omission model for `hCause` of `simplyPriorGroundViaEsseCause`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (SimplyPriorIsCauseOfBeing P C true) ∧
    (SimplePriorityRelatesActualConcreta m true P) ∧
    (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (SimplyPriorIsActualConcreteGround m true P)
end simplyPriorGroundViaEsseCause.omit_hCause

namespace simplyPriorGroundViaEsseCause.omit_hRel
/-- Omission model for `hRel` of `simplyPriorGroundViaEsseCause`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ b => b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (SimplyPriorIsCauseOfBeing P C true) ∧
    ¬ (SimplePriorityRelatesActualConcreta m true P) ∧
    (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (SimplyPriorIsActualConcreteGround m true P)
end simplyPriorGroundViaEsseCause.omit_hRel

namespace simplyPriorGroundViaEsseCause.omit_hEsse
/-- Omission model for `hEsse` of `simplyPriorGroundViaEsseCause`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (SimplyPriorIsCauseOfBeing P C true) ∧
    (SimplePriorityRelatesActualConcreta m true P) ∧
    ¬ (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (SimplyPriorIsActualConcreteGround m true P)
end simplyPriorGroundViaEsseCause.omit_hEsse

namespace necessityCauseGroundViaEsseCause.omit_hCause
/-- Omission model for `hCause` of `necessityCauseGroundViaEsseCause`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (NecessityCauseCausesEsse N C true) ∧
    (NecessityCauseRelataActualConcrete m true N) ∧
    (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (NecessityCausesAreActualConcreteGrounds m true N)
end necessityCauseGroundViaEsseCause.omit_hCause

namespace necessityCauseGroundViaEsseCause.omit_hRel
/-- Omission model for `hRel` of `necessityCauseGroundViaEsseCause`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ b => b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (NecessityCauseCausesEsse N C true) ∧
    ¬ (NecessityCauseRelataActualConcrete m true N) ∧
    (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (NecessityCausesAreActualConcreteGrounds m true N)
end necessityCauseGroundViaEsseCause.omit_hRel

namespace necessityCauseGroundViaEsseCause.omit_hEsse
/-- Omission model for `hEsse` of `necessityCauseGroundViaEsseCause`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (NecessityCauseCausesEsse N C true) ∧
    (NecessityCauseRelataActualConcrete m true N) ∧
    ¬ (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (NecessityCausesAreActualConcreteGrounds m true N)
end necessityCauseGroundViaEsseCause.omit_hEsse

namespace necessityCauseGroundViaDependence.omit_hDep
/-- Omission model for `hDep` of `necessityCauseGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (NecessitatedDependsOnItsCause N D) ∧
    (NecessityCauseRelataActualConcrete m true N) ∧
    (ActualDependenceIsGrounding m true D) ∧
    ¬ (NecessityCausesAreActualConcreteGrounds m true N)
end necessityCauseGroundViaDependence.omit_hDep

namespace necessityCauseGroundViaDependence.omit_hRel
/-- Omission model for `hRel` of `necessityCauseGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ b => b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (NecessitatedDependsOnItsCause N D) ∧
    ¬ (NecessityCauseRelataActualConcrete m true N) ∧
    (ActualDependenceIsGrounding m true D) ∧
    ¬ (NecessityCausesAreActualConcreteGrounds m true N)
end necessityCauseGroundViaDependence.omit_hRel

namespace necessityCauseGroundViaDependence.omit_hGround
/-- Omission model for `hGround` of `necessityCauseGroundViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (NecessitatedDependsOnItsCause N D) ∧
    (NecessityCauseRelataActualConcrete m true N) ∧
    ¬ (ActualDependenceIsGrounding m true D) ∧
    ¬ (NecessityCausesAreActualConcreteGrounds m true N)
end necessityCauseGroundViaDependence.omit_hGround

namespace contingentGroundedViaParticipation.omit_hPart
/-- Omission model for `hPart` of `contingentGroundedViaParticipation`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun w b => w = true ∨ b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (ContingentConcretumParticipatesEsse m true Partic) ∧
    (ParticipatedEsseHasDistinctCause Partic C true) ∧
    (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (EveryContingentGroundedAt m true)
end contingentGroundedViaParticipation.omit_hPart

namespace contingentGroundedViaParticipation.omit_hCause
/-- Omission model for `hCause` of `contingentGroundedViaParticipation`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun w b => w = true ∨ b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun x => x = false
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (ContingentConcretumParticipatesEsse m true Partic) ∧
    ¬ (ParticipatedEsseHasDistinctCause Partic C true) ∧
    (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (EveryContingentGroundedAt m true)
end contingentGroundedViaParticipation.omit_hCause

namespace contingentGroundedViaParticipation.omit_hEsse
/-- Omission model for `hEsse` of `contingentGroundedViaParticipation`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun w b => w = true ∨ b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun x => x = false
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (ContingentConcretumParticipatesEsse m true Partic) ∧
    (ParticipatedEsseHasDistinctCause Partic C true) ∧
    ¬ (EsseCauseIsActualConcreteGround m true C true) ∧
    ¬ (EveryContingentGroundedAt m true)
end contingentGroundedViaParticipation.omit_hEsse

namespace contingentGroundedViaLocalCause.omit_hLocal
/-- Omission model for `hLocal` of `contingentGroundedViaLocalCause`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun w b => w = true ∨ b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (LocalCausalPrinciple m.ontic) ∧
    (ExistingCauseOfActualConcretumIsConcreteGround m true) ∧
    ¬ (EveryContingentGroundedAt m true)
end contingentGroundedViaLocalCause.omit_hLocal

namespace contingentGroundedViaLocalCause.omit_hBridge
/-- Omission model for `hBridge` of `contingentGroundedViaLocalCause`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun w b => w = true ∨ b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ y x => y = true ∧ x = false
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (LocalCausalPrinciple m.ontic) ∧
    ¬ (ExistingCauseOfActualConcretumIsConcreteGround m true) ∧
    ¬ (EveryContingentGroundedAt m true)
end contingentGroundedViaLocalCause.omit_hBridge

namespace contingentGroundedViaDependence.omit_hDep
/-- Omission model for `hDep` of `contingentGroundedViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun w b => w = true ∨ b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (ActualContingentDependsOnActualConcretum m true D) ∧
    (ActualDependenceIsGrounding m true D) ∧
    ¬ (EveryContingentGroundedAt m true)
end contingentGroundedViaDependence.omit_hDep

namespace contingentGroundedViaDependence.omit_hGround
/-- Omission model for `hGround` of `contingentGroundedViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun w b => w = true ∨ b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (ActualContingentDependsOnActualConcretum m true D) ∧
    ¬ (ActualDependenceIsGrounding m true D) ∧
    ¬ (EveryContingentGroundedAt m true)
end contingentGroundedViaDependence.omit_hGround

namespace asymmetricViaPriority.omit_hPrior
/-- Omission model for `hPrior` of `asymmetricViaPriority`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ a b => a ≠ b
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (ActualGroundingIsSimplePriority m true P) ∧
    (PriorityRequiresNonmutualDependence P D) ∧
    ¬ (ActualGroundingAsymmetric m true)
end asymmetricViaPriority.omit_hPrior

namespace asymmetricViaPriority.omit_hReq
/-- Omission model for `hReq` of `asymmetricViaPriority`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ a b => a ≠ b
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun a b => a ≠ b
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (ActualGroundingIsSimplePriority m true P) ∧
    ¬ (PriorityRequiresNonmutualDependence P D) ∧
    ¬ (ActualGroundingAsymmetric m true)
end asymmetricViaPriority.omit_hReq

namespace asymmetricViaDependence.omit_hDep
/-- Omission model for `hDep` of `asymmetricViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ a b => a ≠ b
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (ActualGroundingIsDependence m true D) ∧
    (DependenceForBeingAsymmetric D) ∧
    ¬ (ActualGroundingAsymmetric m true)
end asymmetricViaDependence.omit_hDep

namespace asymmetricViaDependence.omit_hAsym
/-- Omission model for `hAsym` of `asymmetricViaDependence`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ a b => a ≠ b
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun x y => x ≠ y
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (ActualGroundingIsDependence m true D) ∧
    ¬ (DependenceForBeingAsymmetric D) ∧
    ¬ (ActualGroundingAsymmetric m true)
end asymmetricViaDependence.omit_hAsym

namespace asymmetricViaGrades.omit_hMore
/-- Omission model for `hMore` of `asymmetricViaGrades`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ a b => a ≠ b
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (ActualGroundIsMoreInEsse m true More true) ∧
    (MoreInIsAsymmetric More) ∧
    ¬ (ActualGroundingAsymmetric m true)
end asymmetricViaGrades.omit_hMore

namespace asymmetricViaGrades.omit_hAsym
/-- Omission model for `hAsym` of `asymmetricViaGrades`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ a b => a ≠ b
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ a b => a ≠ b
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    (ActualGroundIsMoreInEsse m true More true) ∧
    ¬ (MoreInIsAsymmetric More) ∧
    ¬ (ActualGroundingAsymmetric m true)
end asymmetricViaGrades.omit_hAsym

namespace atMaximalTargetViaGrades.omit_hMore
/-- Omission model for `hMore` of `atMaximalTargetViaGrades`: the other premises hold and the conclusion fails. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun _ _ => True
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev gr : Bool → Bool → Bool → Prop := fun _ a b => a ≠ b
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev D : Bool → Bool → Prop := fun _ _ => False
abbrev P : Bool → Bool → Prop := fun _ _ => False
abbrev N : Bool → Bool → Prop := fun _ _ => False
abbrev Partic : Bool → Prop := fun _ => False
abbrev More : Bool → Bool → Bool → Prop := fun _ _ _ => False
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- The omission condition. -/
def Holds : Prop :=
    ¬ (ActualGroundIsMoreInEsse m true More true) ∧
    ¬ (AtMaximalTarget m true Act More true)
end atMaximalTargetViaGrades.omit_hMore

namespace witness
/-- Joint nonvacuity witness: an actual contingent concretum (`false`, absent at world `false`) grounded by a necessary one (`true`); every relation is nonempty. -/
abbrev acc : Bool → Bool → Prop := fun _ _ => True
abbrev ex : Bool → Bool → Prop := fun w b => w = true ∨ b = true
abbrev conc : Bool → Prop := fun _ => True
abbrev cau : Bool → Bool → Bool → Prop := fun _ y x => y = true ∧ x = false
abbrev gr : Bool → Bool → Bool → Prop := fun _ y x => y = true ∧ x = false
abbrev m : Profile Bool Bool := mk acc ex conc cau gr
abbrev C : Bool → Bool → Bool → Prop := fun c x r => c = true ∧ x = false ∧ r = true
abbrev D : Bool → Bool → Prop := fun x c => x = false ∧ c = true
abbrev P : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev N : Bool → Bool → Prop := fun y x => y = true ∧ x = false
abbrev Partic : Bool → Prop := fun x => x = false
abbrev More : Bool → Bool → Bool → Prop := fun _ a b => a = true ∧ b = false
abbrev Act : Bool → Bool → Prop := fun _ _ => True
/-- Every premise (restricted well-foundedness excepted) and every conclusion of the batch holds, with nonempty relations. -/
def Holds : Prop :=
    (EsseCausesExistAt m true C true) ∧
    (EsseCausesAreConcrete m C true) ∧
    (EsseEffectDependsOnItsCause C true D) ∧
    (ActualDependenceIsGrounding m true D) ∧
    (EsseCauseIsActualConcreteGround m true C true) ∧
    (PriorityRequiresNonmutualDependence P D) ∧
    (SimplePriorityRelatesActualConcreta m true P) ∧
    (SimplyPriorIsActualConcreteGround m true P) ∧
    (SimplyPriorIsCauseOfBeing P C true) ∧
    (EsseCauseIsActualConcreteGround m true C true) ∧
    (NecessityCauseCausesEsse N C true) ∧
    (NecessityCauseRelataActualConcrete m true N) ∧
    (NecessityCausesAreActualConcreteGrounds m true N) ∧
    (NecessitatedDependsOnItsCause N D) ∧
    (ContingentConcretumParticipatesEsse m true Partic) ∧
    (ParticipatedEsseHasDistinctCause Partic C true) ∧
    (EveryContingentGroundedAt m true) ∧
    (LocalCausalPrinciple m.ontic) ∧
    (ExistingCauseOfActualConcretumIsConcreteGround m true) ∧
    (ActualContingentDependsOnActualConcretum m true D) ∧
    (ActualGroundingIsSimplePriority m true P) ∧
    (ActualGroundingAsymmetric m true) ∧
    (ActualGroundingIsDependence m true D) ∧
    (DependenceForBeingAsymmetric D) ∧
    (ActualGroundIsMoreInEsse m true More true) ∧
    (MoreInIsAsymmetric More) ∧
    (AtMaximalTarget m true Act More true) ∧
    ContingentAt m.ontic true false ∧
    m.grounds true true false ∧
    C true false true ∧
    D false true ∧
    P true false ∧
    N true false ∧
    Partic false ∧
    More true true false ∧
    m.ontic.Causes true true false
end witness

/-- The batch controls: one omission model per premise of each derivation (the
well-foundedness omission for `asymmetricFromWF` is `wf.Holds`) and one joint
nonvacuity witness. -/
def Certificate : Prop :=
  wf.Holds ∧
  esseCauseGroundViaDependence.omit_hGround.Holds ∧
  esseCauseGroundViaDependence.omit_hExists.Holds ∧
  esseCauseGroundViaDependence.omit_hConcrete.Holds ∧
  esseCauseGroundViaDependence.omit_hDep.Holds ∧
  simplyPriorGroundViaDependence.omit_hReq.Holds ∧
  simplyPriorGroundViaDependence.omit_hRel.Holds ∧
  simplyPriorGroundViaDependence.omit_hGround.Holds ∧
  simplyPriorGroundViaEsseCause.omit_hCause.Holds ∧
  simplyPriorGroundViaEsseCause.omit_hRel.Holds ∧
  simplyPriorGroundViaEsseCause.omit_hEsse.Holds ∧
  necessityCauseGroundViaEsseCause.omit_hCause.Holds ∧
  necessityCauseGroundViaEsseCause.omit_hRel.Holds ∧
  necessityCauseGroundViaEsseCause.omit_hEsse.Holds ∧
  necessityCauseGroundViaDependence.omit_hDep.Holds ∧
  necessityCauseGroundViaDependence.omit_hRel.Holds ∧
  necessityCauseGroundViaDependence.omit_hGround.Holds ∧
  contingentGroundedViaParticipation.omit_hPart.Holds ∧
  contingentGroundedViaParticipation.omit_hCause.Holds ∧
  contingentGroundedViaParticipation.omit_hEsse.Holds ∧
  contingentGroundedViaLocalCause.omit_hLocal.Holds ∧
  contingentGroundedViaLocalCause.omit_hBridge.Holds ∧
  contingentGroundedViaDependence.omit_hDep.Holds ∧
  contingentGroundedViaDependence.omit_hGround.Holds ∧
  asymmetricViaPriority.omit_hPrior.Holds ∧
  asymmetricViaPriority.omit_hReq.Holds ∧
  asymmetricViaDependence.omit_hDep.Holds ∧
  asymmetricViaDependence.omit_hAsym.Holds ∧
  asymmetricViaGrades.omit_hMore.Holds ∧
  asymmetricViaGrades.omit_hAsym.Holds ∧
  atMaximalTargetViaGrades.omit_hMore.Holds ∧
  witness.Holds

end Control

end TruthCore.Causality.Round2Grounding
