import TruthCore.Explanation.PSRStrength
import TruthCore.Causality.NecessarilyUnderived
import TruthCore.Logic.CogitoConcrete
import TruthCore.Logic.ExcludedMiddle

/-! Source-free empty-bearer branch only. Arena, world-relative existence,
facts and fact truth retain their existing meanings. The extra CauseFact
parameter has type World → Being → Fact → Prop and is NOT Arena.explains or
Ontic.Causes. No fact is reified as an individual; no beginning is required.

Application to a negative EVER-history situation remains OPEN: the fixed-fact
meaning and history/existence correspondence are explicit commitments, not
consequences of ordinary now-slice presence. -/
namespace TruthCore.Explanation.EmptyHistoryCausalAvailability
open TruthCore.Explanation.PSRStrength (Arena Contingent)
open TruthCore.German.Kant.CosmologicalInference (ContingentAt NecessaryAt)
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)
open TruthCore.Logic (ExcludedMiddle)
open TruthCore.Modal (Euclidean)
open TruthCore.Causality.NecessarilyUnderived (ActualReflexive)

/-- No concrete candidate is actually contingent at the specified world.
It permits an empty concrete extension or existing necessary concreta. -/
def NoContingentConcreteAt {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (v : W) : Prop :=
  ∀ b, Concrete b → ¬ ContingentAt A.ontic v b

/-- The SAME fact obtains and has an actual concrete causal bearer in the
same world. CauseFact remains a separate supplied individual-to-fact relation.
No sufficiency, priority, causation-grounding identity or explanation law. -/
def ActualCausedFact {W B F : Type} (A : Arena W B F) (Concrete : B → Prop)
    (CauseFact : W → B → F → Prop) (v : W) (f : F) : Prop :=
  A.holds v f ∧ ∃ c, Concrete c ∧ A.ontic.ExistsAt v c ∧ CauseFact v c f

/-- Individual possible causal coverage of obtaining contingent facts at v.
The fact identity is retained across worlds. This is NOT Arena.WeakPSR:
its witnesses are actual concrete causal individuals, not fact-reasons. -/
def WeakActualConcreteCausalAvailabilityAt {W B F : Type}
    (A : Arena W B F) (Concrete : B → Prop) (CauseFact : W → B → F → Prop)
    (v : W) : Prop :=
  ∀ f, Contingent A v f → ∃ u, A.ontic.frame.access v u ∧
    ActualCausedFact A Concrete CauseFact u f

/-- OPEN admission/preservation: a supplied fixed fact is true exactly where
there are no actual contingent concreta. Historical EVER-existence is not
built into Ontic.ExistsAt by this definition. -/
def NegativeFactMeaning {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (f : F) : Prop :=
  ∀ v, A.holds v f ↔ NoContingentConcreteAt A Concrete v

/-- THREE commitments packaged explicitly: an accessible selected world,
absence of contingent concreta there, and individual weak causal availability
there. This is the empty-bearer branch, not absence of contingent situations. -/
def AccessibleEmptyCoverage {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (CauseFact : W → B → F → Prop) (w : W) : Prop :=
  ∃ v, A.ontic.frame.access w v ∧ NoContingentConcreteAt A Concrete v ∧
    WeakActualConcreteCausalAvailabilityAt A Concrete CauseFact v

/-- An accessible world has an actual concrete individual, reusing the
existing InhabitedConcreteAt predicate. It need not be the coverage world. -/
def PossiblyInhabitedConcreteAt {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (w : W) : Prop :=
  ∃ v, A.ontic.frame.access w v ∧ InhabitedConcreteAt A.ontic Concrete v

/-- Small pointwise consequence of represented noncontingency, with explicit
EM. Existing external-candidate machinery uses a Scenario adapter and classical
axioms unnecessarily for this fact-arena argument; this lemma preserves the
same Ontic without a new carrier or unused positive-beginning fields. -/
theorem necessaryOfActualNoncontingent {W B F : Type} (A : Arena W B F)
    (Concrete : B → Prop) (v : W) (c : B) (hEM : ExcludedMiddle)
    (hNoCont : NoContingentConcreteAt A Concrete v)
    (hc : Concrete c) (he : A.ontic.ExistsAt v c) : NecessaryAt A.ontic v c := by
  intro u hvu
  rcases hEM (A.ontic.ExistsAt u c) with hPresent | hAbsent
  · exact hPresent
  · exact (hNoCont c hc ⟨he, u, hvu, hAbsent⟩).elim

/-- The selected origin's accessible component is closed under another step.
Only Euclideanness and reflexivity at that origin are needed, not global T/4. -/
theorem accessibleSecondStep {W B F : Type} (A : Arena W B F) (w v u : W)
    (hEuclidean : Euclidean A.ontic.frame) (hReflexive : ActualReflexive A.ontic w)
    (hwv : A.ontic.frame.access w v) (hvu : A.ontic.frame.access v u) :
    A.ontic.frame.access w u :=
  hEuclidean v w u (hEuclidean w v w hwv hReflexive) hvu

/-- Transfer the SAME individual's necessary existence at an accessible world
back to actual existence and necessity at the selected origin. -/
theorem necessaryAtOrigin {W B F : Type} (A : Arena W B F) (w v : W) (c : B)
    (hEuclidean : Euclidean A.ontic.frame) (hReflexive : ActualReflexive A.ontic w)
    (hwv : A.ontic.frame.access w v) (hn : NecessaryAt A.ontic v c) :
    A.ontic.ExistsAt w c ∧ NecessaryAt A.ontic w c :=
  ⟨hn w (hEuclidean w v w hwv hReflexive),
    fun z hwz => hn z (hEuclidean w v z hwv hwz)⟩

end TruthCore.Explanation.EmptyHistoryCausalAvailability
