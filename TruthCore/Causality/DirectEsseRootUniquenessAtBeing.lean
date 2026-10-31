import TruthCore.Causality.WholeRosterFoundation
import TruthCore.Causality.DirectEsseRootRoute
import TruthCore.Causality.NecessaryRootUniqueness
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
import TruthCore.Models.QuartaViaMaximumControls

/-! Fixed-esse instances of existing causal/maximum interfaces. The new grades
interface restricts a quantifier; it neither assumes uniqueness nor defends the
existence of a real metaphysical maximum. No source reading is changed. -/
namespace TruthCore.Causality.DirectEsseRootUniquenessAtBeing
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- OPEN fixed-esse grades-to-maximum instance. It says nothing about any other
respect and requires a maximum only when this respect has a comparison. -/
def GradesToMaximumAtBeing {B R : Type} (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R) : Prop :=
  (∃ x y, MoreIn esse x y) → ∃ n, IsMaximumIn InAct MoreIn esse n

theorem restrictGrades {B R : Type} (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (esse : R)
    (h : GradesByApproachToAMaximumReading InAct MoreIn) :
    GradesToMaximumAtBeing InAct MoreIn esse := h esse

theorem restrictGenus {B R : Type} (InAct : B → R → Prop)
    (MoreIn : R → B → B → Prop) (CausesIn : B → B → R → Prop) (esse : R)
    (h : MaximumInGenusCausesAllInGenusReading InAct MoreIn CausesIn) :
    MaximumInBeingCausesAllBeingsReading InAct MoreIn CausesIn esse := h esse

namespace Controls
abbrev act := TruthCore.Models.QuartaViaMaximumControls.CrossedTops.inAct
abbrev esse : Bool := true
/-- Newly supplied complete-history ontology on the existing Boolean carrier.
Its selected grounds are the OLD esse-causes. All candidates are present and
concrete; no real ontology/existential adequacy is inferred from this fixture. -/
def model : TruthCore.Causality.BruteFoundationBoundary.Profile Bool Bool where
  ontic := { frame := ⟨fun _ _ => True⟩
             ExistsAt := fun _ _ => True
             Causes := fun _ c x => TruthCore.Models.QuartaViaMaximumControls.CrossedTops.causesIn c x esse }
  concrete := fun _ => True
  grounds := fun _ c x => TruthCore.Models.QuartaViaMaximumControls.CrossedTops.causesIn c x esse

/-- Preserve OLD esse grades. Only the nonesse dictionary is newly assigned:
false means no comparisons there; true means every pair compares there. -/
def more (loops r y x : Bool) : Prop :=
  Bool.rec (motive := fun _ => Prop) (loops = true) (TruthCore.Models.QuartaViaMaximumControls.CrossedTops.moreIn true y x) r
/-- Preserve OLD esse-causation and newly assign no nonesse causation. -/
def causes (c x r : Bool) : Prop := r = true ∧ TruthCore.Models.QuartaViaMaximumControls.CrossedTops.causesIn c x true

/-- Seven nonlogical inputs of the fixed-esse eight-input uniqueness route;
EM is retained explicitly by the registered control theorem. -/
def Retained (loops : Bool) : Prop :=
  TruthCore.Logic.CogitoConcrete.InhabitedConcreteAt model.ontic model.concrete false ∧
  TruthCore.Causality.WholeRosterFoundation.WholeRosterNotTrapped model false ∧
  TruthCore.Causality.BruteFoundationBoundary.EveryContingentGroundedAt model false ∧
  MaximumInBeingCausesAllBeingsReading act (more loops) causes esse ∧
  TruthCore.Causality.ExistenceActuality.ExistingInActAt model.ontic act esse false ∧
  TruthCore.Causality.NecessaryConcreteRouteBridge.EsseCauseIsActualConcreteGround
    model false causes esse ∧ GradesToMaximumAtBeing act (more loops) esse

/-- Two complete same-esse assignments keep all new inputs, a positive esse
grade, actual population and the unique necessary actual root. One fails only
the global causal requirement while keeping global grades-to-maximum; the other
fails global grades-to-maximum while keeping global genus causality (vacuously
at the nonesse respect with no maxima). Its universal nonesse comparison has
self-loops; separation is only for unconstrained MoreIn, not strict-order
semantics or metaphysical plausibility. No order laws on MoreIn are assumed. -/
def ScopeControls : Prop :=
  Retained false ∧ more false esse false true ∧
  GradesByApproachToAMaximumReading act (more false) ∧
  ¬ MaximumInGenusCausesAllInGenusReading act (more false) causes ∧
  Retained true ∧ more true esse false true ∧
  MaximumInGenusCausesAllInGenusReading act (more true) causes ∧
  ¬ GradesByApproachToAMaximumReading act (more true) ∧
  TruthCore.Causality.NecessaryRootUniqueness.UniqueNecessaryActualRootAt model false
end Controls
end TruthCore.Causality.DirectEsseRootUniquenessAtBeing
