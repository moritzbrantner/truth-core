import TruthCore.Logic.ExcludedMiddle
import TruthCore.Logic.Configuration
import TruthCore.Results.Kant.CosmologicalInference.WellFoundedCausesBlockAllContingent.Solution

/-!
# #487: an actual concrete causal root and modal necessity

These are analyst-defined conditionals, not source-attributed metaphysics.
Worlds are complete alternative histories, not time instants. Individual
identity is rigid across the fixed candidate type. `Causes` is the Kantian
generic causal relation; reading it as existence-grounding, efficient event
causation or actualization requires separate philosophical justification.

The existing well-founded causal-regress proof is consumed below. In
particular, the typed result requires dependence only at the *selected*
world, not at every world, and well-foundedness only among the *actually
existing concrete* candidates. Excluded middle is a visible premise, never
an implicit Lean classical axiom.
-/

namespace TruthCore.Causality.NecessaryConcreteRoot

open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic
open TruthCore.Results.Kant.CosmologicalInference.WellFoundedCausesBlockAllContingent

variable {W E : Type}

/-- Candidates known to be concrete and present in the selected complete
history. The *same* underlying `E` is used to evaluate them at other worlds. -/
def ActualConcrete (m : Ontic W E) (concrete : E → Prop) (w : W) : Type :=
  {x : E // concrete x ∧ m.ExistsAt w x}

/-- Actual concrete population, distinct from mere world-type inhabitation. -/
def PopulatedConcreteAt (m : Ontic W E) (concrete : E → Prop) (w : W) : Prop :=
  ∃ x, concrete x ∧ m.ExistsAt w x

/-- Only causal edges between actual concrete individuals are considered
for well-foundedness. No absent or abstract predecessor can enter this type. -/
def ActualConcreteCausesAt (m : Ontic W E) (concrete : E → Prop) (w : W) :
    ActualConcrete m concrete w → ActualConcrete m concrete w → Prop :=
  fun y x => m.Causes w y.val x.val

/-- Well-foundedness on the *typed actual-concrete* causal relation only. -/
def WellFoundedConcreteAt (m : Ontic W E) (concrete : E → Prop) (w : W) : Prop :=
  WellFounded (ActualConcreteCausesAt m concrete w)

/-- Root-inclusive dependence: every actual contingent concrete individual
has an immediate predecessor that is itself concrete and actual. The relation
is supplied and may be causation or grounding, but not silently both. -/
def ContingentConcreteDependenceAt (m : Ontic W E)
    (concrete : E → Prop) (w : W) : Prop :=
  ∀ x, concrete x → m.ExistsAt w x → ContingentAt m w x →
    ∃ y, concrete y ∧ m.ExistsAt w y ∧ m.Causes w y x

/-- One and the same actual concrete bearer exists in every world accessible
from the evaluation world. This is not yet existence at *every* world. -/
def NecessaryConcreteAt (m : Ontic W E) (concrete : E → Prop) (w : W) : Prop :=
  ∃ x, concrete x ∧ m.ExistsAt w x ∧ NecessaryAt m w x

/-- The additional modal bridge from the selected world's accessible
histories to *all* worlds in the supplied universe. -/
def UniversalAccessibilityAt (m : Ontic W E) (w : W) : Prop :=
  ∀ v, m.frame.access w v

/-- One fixed actual concrete individual is present in every world of `W`,
including any worlds inaccessible from the selected world. -/
def EveryWorldConcreteAt (m : Ontic W E) (concrete : E → Prop) (w : W) : Prop :=
  ∃ x, concrete x ∧ m.ExistsAt w x ∧ ∀ v, m.ExistsAt v x

/-- Exact negation of the positive conclusion in the selected semantics. -/
def AllActualConcreteContingent (m : Ontic W E)
    (concrete : E → Prop) (w : W) : Prop :=
  ∀ x, concrete x → m.ExistsAt w x → ContingentAt m w x

/-- Restrict the old `Ontic` signature to the actual-concrete carrier, while
preserving its world frame and its original cross-world existence facts. -/
private def restrictedOntic (m : Ontic W E) (concrete : E → Prop) (w : W) :
    Ontic W (ActualConcrete m concrete w) where
  frame := m.frame
  ExistsAt := fun v x => m.ExistsAt v x.val
  Causes := fun v y x => m.Causes v y.val x.val

/-- Consequence of the *existing* well-founded regress induction under only
actual-world typed dependence. It remains constructive. -/
private theorem notAllActualConcreteContingent
    (m : Ontic W E) (concrete : E → Prop) (w : W)
    (hPop : ∃ x, concrete x ∧ m.ExistsAt w x)
    (hWF : WellFounded (ActualConcreteCausesAt m concrete w))
    (hDep : ContingentConcreteDependenceAt m concrete w) :
    ¬ ∀ x : ActualConcrete m concrete w,
      (restrictedOntic m concrete w).ExistsAt w x →
        ContingentAt (restrictedOntic m concrete w) w x := by
  have hLocal : ∀ x : ActualConcrete m concrete w,
      ContingentAt (restrictedOntic m concrete w) w x →
        ∃ y, (restrictedOntic m concrete w).ExistsAt w y ∧
          (restrictedOntic m concrete w).Causes w y x := by
    intro x hx
    change ContingentAt m w x.val at hx
    obtain ⟨y, hyConcrete, hyExists, hyCause⟩ :=
      hDep x.val x.property.1 x.property.2 hx
    exact ⟨⟨y, ⟨hyConcrete, hyExists⟩⟩, hyExists, hyCause⟩
  have hPresent : ∃ x : ActualConcrete m concrete w,
      (restrictedOntic m concrete w).ExistsAt w x := by
    obtain ⟨x, hc, he⟩ := hPop
    exact ⟨⟨x, ⟨hc, he⟩⟩, he⟩
  exact wellFoundedCausesBlockAllContingentAt
    (restrictedOntic m concrete w) w hLocal hWF hPresent

/-- Excluded middle gives a counterexample to a false universal. The logical
principle is explicit, so this lemma and its consumers have zero axioms. -/
private theorem existsNotOfNotAll {A : Type} (hEM : ExcludedMiddle)
    (p : A → Prop) (hNot : ¬ ∀ x, p x) : ∃ x, ¬ p x := by
  cases hEM (∃ x, ¬ p x) with
  | inl hExists => exact hExists
  | inr hNone =>
    exfalso
    apply hNot
    intro x
    cases hEM (p x) with
    | inl hp => exact hp
    | inr hnp => exact False.elim (hNone ⟨x, hnp⟩)

/-- A negative universal on Kantian contingency implies a fixed accessible-
world necessary witness, with excluded middle as an explicit premise. -/
private theorem necessaryOfNotAll (hEM : ExcludedMiddle)
    (m : Ontic W E) (w : W)
    (hNot : ¬ ∀ x, m.ExistsAt w x → ContingentAt m w x) :
    NecessaryBeing m w := by
  obtain ⟨x, hx⟩ := existsNotOfNotAll hEM
    (fun x => m.ExistsAt w x → ContingentAt m w x) hNot
  have hExists : m.ExistsAt w x := by
    cases hEM (m.ExistsAt w x) with
    | inl he => exact he
    | inr hn => exact False.elim (hx (fun he => False.elim (hn he)))
  have hNotCont : ¬ ContingentAt m w x := by
    intro hc
    exact hx (fun _ => hc)
  refine ⟨x, hExists, ?_⟩
  intro v hv
  cases hEM (m.ExistsAt v x) with
  | inl he => exact he
  | inr hn => exact False.elim (hNotCont ⟨hExists, ⟨v, hv, hn⟩⟩)

/-- The strongest existential consequence under the *original* untyped
global local-causality assumptions, relative to accessible worlds only. -/
def KantRegressYieldsNecessary : Prop :=
  ∀ (World Entity : Type) (m : Ontic World Entity) (w : World),
    ExcludedMiddle → LocalCausalPrinciple m →
      WellFounded (m.Causes w) → (∃ x, m.ExistsAt w x) →
        NecessaryBeing m w

theorem kantRegressYieldsNecessary : KantRegressYieldsNecessary := by
  intro World Entity m w hEM hLocal hWF hPop
  exact necessaryOfNotAll hEM m w
    (wellFoundedCausesBlockAllContingent World Entity m w hLocal hWF hPop)

/-- Root-inclusive local dependence plus well-founded ancestry and an actual
concrete existent imply an *accessible-world* necessary concretum. -/
def ConcreteRootConditional : Prop :=
  ∀ (World Entity : Type) (m : Ontic World Entity)
    (concrete : Entity → Prop) (w : World),
    ExcludedMiddle →
      (∃ x, concrete x ∧ m.ExistsAt w x) →
        WellFounded (ActualConcreteCausesAt m concrete w) →
          ContingentConcreteDependenceAt m concrete w →
            NecessaryConcreteAt m concrete w

theorem concreteRootConditional : ConcreteRootConditional := by
  intro World Entity m concrete w hEM hPop hWF hDep
  obtain ⟨x, hx, hNecessary⟩ := necessaryOfNotAll hEM
    (restrictedOntic m concrete w) w
    (notAllActualConcreteContingent m concrete w hPop hWF hDep)
  exact ⟨x.val, x.property.1, x.property.2, hNecessary⟩

/-- Actual-world accessibility must cover all worlds to upgrade the same
witness from `NecessaryAt` to unrestricted global existence. -/
def GlobalConcreteRootConditional : Prop :=
  ∀ (World Entity : Type) (m : Ontic World Entity)
    (concrete : Entity → Prop) (w : World),
    ExcludedMiddle →
      UniversalAccessibilityAt m w →
        (∃ x, concrete x ∧ m.ExistsAt w x) →
          WellFounded (ActualConcreteCausesAt m concrete w) →
            ContingentConcreteDependenceAt m concrete w →
              EveryWorldConcreteAt m concrete w

theorem globalConcreteRootConditional : GlobalConcreteRootConditional := by
  intro World Entity m concrete w hEM hAllAccessible hPop hWF hDep
  obtain ⟨x, hc, he, hn⟩ :=
    concreteRootConditional World Entity m concrete w hEM hPop hWF hDep
  exact ⟨x, hc, he, fun v => hn v (hAllAccessible v)⟩

/-- A four-commitment inconsistent core, proved *constructively*: inhabited
actual concrete extension, well-founded concrete ancestry, universal actual
contingent-dependence, and the negation of any necessary concrete bearer
(expressed as every actual concretum being contingent).

Its premises concern complete histories, not a finite past, nor a universal
cause of the entire history. Minimality needs independent omission models. -/
def ConcreteRootCoreInconsistent : Prop :=
  ∀ (World Entity : Type) (m : Ontic World Entity)
    (concrete : Entity → Prop) (w : World),
    (∃ x, concrete x ∧ m.ExistsAt w x) →
      WellFounded (ActualConcreteCausesAt m concrete w) →
        ContingentConcreteDependenceAt m concrete w →
          AllActualConcreteContingent m concrete w → False

theorem concreteRootCoreInconsistent : ConcreteRootCoreInconsistent := by
  intro World Entity m concrete w hPop hWF hDep hAll
  exact (notAllActualConcreteContingent m concrete w hPop hWF hDep)
    (fun x _ => hAll x.val x.property.1 x.property.2)

/-- Configuration-elimination entrypoint with four *independent statement*
premises and the existing repository conclusion type `ConfigurationFalse`.
The four inputs share exactly one frame, roster, concreteness predicate,
causal relation and evaluation world; no statement is smuggled by a label. -/
theorem actualConcreteCoreFalse (m : Ontic W E) (concrete : E → Prop) (w : W)
    (hPop : PopulatedConcreteAt m concrete w)
    (hWF : WellFoundedConcreteAt m concrete w)
    (hDep : ContingentConcreteDependenceAt m concrete w)
    (hAll : AllActualConcreteContingent m concrete w) :
    TruthCore.Logic.ConfigurationFalse := by
  exact concreteRootCoreInconsistent W E m concrete w hPop hWF hDep hAll

end TruthCore.Causality.NecessaryConcreteRoot
