module

public import TruthCore.Causality.NecessarySupportCoverage
public import TruthCore.Causality.ActualUnderivedEssenceEsse

/-!
# J1 at the selected world only

Analyst formulations, attribution deferred. Target: premise J1 of the modal
spine's join, `NoContingentConcreteSupport` (`STMT-NO-CONTINGENT-CONCRETE-SUPPORT`),
on the routes to `STMT-NECESSARY-CONCRETE-UNDERIVED-AT`.

J1 quantifies over every carrier world `v`: a concretum existing at `v` that
supports, at `v`, a concretum necessary from `w` is necessary from `w`. Its
selected-world instance `ActualNoContingentConcreteSupport` constrains only
supporters existing at `w` and support edges at `w`. It is the existing
selected-world restriction `ActualUnderivedEssenceEsse.ActualNoContingent`
(`STMT-ACTUAL-NO-CONTINGENT`) instantiated on the concrete subtype, exactly as J1
is `NoContingentGroundOfNecessary` instantiated there. The named wrapper is kept
so that J1 and its instance form one strength-ordered pair on the same concrete
domain; it adds no content to `ActualNoContingent`.

Two finite interpretations, both over the three labels of
`NecessarySupportCoverage.Control.Tri` and two worlds with universal access,
`t2` existing only at `true`:

* `offWorldContingent`: at `false`, `t0` supports `t1`; at `true`, `t2` supports
  `t1`. J1 at `false` fails, its selected-world instance holds, and with coverage
  the join's endpoint holds (witness `t0`).
* `lateSupport`: at `false`, `t0` supports `t1`; at `true`, `t2` supports `t0`.
  The selected-world instance holds with every other premise of the two existing
  J1 routes (`NecessaryConcreteUnderived.checks` and
  `NecessaryConcreteUnderivedFromNecessity.underived`), while J1, coverage and
  the endpoint fail. So the instance can replace J1 on the coverage route but not
  on those two J2 routes.
-/

@[expose] public section

namespace TruthCore.Causality.NecessarySupportActualScope

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.NecessarySupportCoverage
open TruthCore.Causality.ActualUnderivedEssenceEsse (ActualNoContingent)
open TruthCore.German.Kant.CosmologicalInference (Ontic NecessaryAt ContingentAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B : Type}

/-- J1 at the selected world only: every concretum existing at `w` that supports,
at `w`, a concretum necessary from `w` is itself necessary from `w`. Supporters
existing only at other worlds, and support edges at other worlds, are not
constrained. The existing `ActualNoContingent` on the concrete subtype. -/
def ActualNoContingentConcreteSupport (m : Profile W B) (w : W) : Prop :=
  ActualNoContingent (concreteOntic m) (concreteSupport m) w

namespace Control

open TruthCore.Causality.NecessarySupportCoverage.Control (Tri)

/-- Two worlds with universal access; `t0` and `t1` exist at both, `t2` only at
`true`. No generic causes. Shared by both controls. -/
def ontic : Ontic Bool Tri where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun v x => x = .t2 → v = true
  Causes := fun _ _ _ => False

/-- At `false`, `t0` supports `t1`; at `true`, the contingent `t2` supports `t1`. -/
def offWorldContingent : Profile Bool Tri where
  ontic := ontic
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests the world scope of J1, not the concrete/abstract line)
  grounds := fun v a b =>
    (v = false ∧ a = .t0 ∧ b = .t1) ∨ (v = true ∧ a = .t2 ∧ b = .t1)

/-- At `false`, `t0` supports `t1`; at `true`, the contingent `t2` supports `t0`. -/
def lateSupport : Profile Bool Tri where
  ontic := ontic
  concrete := fun _ => True  -- category-constant: intended (all-concrete inventory: the model tests the world scope of J1, not the concrete/abstract line)
  grounds := fun v a b =>
    (v = false ∧ a = .t0 ∧ b = .t1) ∨ (v = true ∧ a = .t2 ∧ b = .t0)

/-- Strictness and route control: J1 fails at `false` while its selected-world
instance holds, together with every premise of the selected-world coverage route
(a necessary concretum, well-founded actual grounding, coverage, excluded middle)
and every premise of `NecessaryConcreteUnderived.checks` other than J1; the
join's endpoint holds. The recorded replaceable-support rival
`SomeNecessaryConcretumContingentlySupported` holds here as well. -/
def OffWorldContingentControl : Prop :=
  ActualNoContingentConcreteSupport offWorldContingent false ∧
    ¬ NoContingentConcreteSupport offWorldContingent false ∧
    TruthCore.Causality.SpineRivalsRootEsse.SomeNecessaryConcretumContingentlySupported
      offWorldContingent false ∧
    NecessaryConcreteAt offWorldContingent false ∧
    InhabitedConcreteAt offWorldContingent.ontic offWorldContingent.concrete false ∧
    ActualGroundingWF offWorldContingent false ∧
    EveryContingentGroundedAt offWorldContingent false ∧
    ActualReflexive offWorldContingent.ontic false ∧
    ConcreteNecessaryUnionWF offWorldContingent false ∧
    NecessarySupportActuallyCovered offWorldContingent false ∧ ExcludedMiddle ∧
    NecessaryConcreteUnderivedAt offWorldContingent false

/-- Insufficiency control: the selected-world instance of J1 holds with every
other premise of `NecessaryConcreteUnderived.checks` and of
`NecessaryConcreteUnderivedFromNecessity.underived` (including J2), and with
the other two premises of `coverageOfNoContingentNoNovel` (reflexive access and
the one-way no-novel-edge condition), while J1, coverage and the join's endpoint
fail. -/
def LateSupportControl : Prop :=
  ActualNoContingentConcreteSupport lateSupport false ∧
    NecessaryConcreteAt lateSupport false ∧
    InhabitedConcreteAt lateSupport.ontic lateSupport.concrete false ∧
    ActualGroundingWF lateSupport false ∧
    EveryContingentGroundedAt lateSupport false ∧
    ActualReflexive lateSupport.ontic false ∧
    ConcreteNecessaryUnionWF lateSupport false ∧ ExcludedMiddle ∧
    NoNovelNecessarySupport (concreteOntic lateSupport) (concreteSupport lateSupport) false ∧
    ¬ NoContingentConcreteSupport lateSupport false ∧
    ¬ NecessarySupportActuallyCovered lateSupport false ∧
    ¬ NecessaryConcreteUnderivedAt lateSupport false

/-- Both controls. -/
def Controls : Prop := OffWorldContingentControl ∧ LateSupportControl

end Control

end TruthCore.Causality.NecessarySupportActualScope
