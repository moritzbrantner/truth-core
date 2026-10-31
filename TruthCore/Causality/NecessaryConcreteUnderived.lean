import TruthCore.Causality.NecessaryRootFork
import TruthCore.Causality.NecessarilyUnderived

/-!
Source-free composition of #487/#553 with #495/#542. Restrict the existing
ontology to concrete candidates; do not identify generic efficient causes with
existential grounding. The same selected `Profile.grounds` relation is used
throughout. Concrete is the existing profile parameter, not a new definition of
physicality. All structural/metaphysical hypotheses remain open.
-/
namespace TruthCore.Causality.NecessaryConcreteUnderived

open TruthCore.Causality.BruteFoundationBoundary
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessaryRootFork
open TruthCore.Logic.CogitoConcrete (InhabitedConcreteAt)

variable {W B : Type}

/-- Carrier restriction only. Existence, accessibility and generic causes are
inherited without strengthening; the subtype retains each concrete candidate's
literal cross-world identity. -/
def concreteOntic (m : Profile W B) : Ontic W {b // m.concrete b} where
  frame := m.ontic.frame
  ExistsAt w b := m.ontic.ExistsAt w b.val
  Causes w a b := m.ontic.Causes w a.val b.val

/-- The original selected existential-grounding relation on concrete candidates.
This does not assert that its ends exist or identify it with `Ontic.Causes`. -/
def concreteSupport (m : Profile W B) (w : W)
    (a b : {b // m.concrete b}) : Prop := m.grounds w a.val b.val

/-- Every existing concrete supporter of a necessary concrete target is itself
necessary. Merely having a necessary target does not establish this premise. -/
def NoContingentConcreteSupport (m : Profile W B) (w : W) : Prop :=
  NoContingentGroundOfNecessary (concreteOntic m) (concreteSupport m) w

/-- The union over all admitted worlds of selected support edges between
necessary concrete candidates is well-founded. Stronger than each world's
acyclicity; it does not require edges to be invariant between worlds. -/
def ConcreteNecessaryUnionWF (m : Profile W B) (w : W) : Prop :=
  WellFoundedUnionNecessarySupport (concreteOntic m) (concreteSupport m) w

/-- One actual concrete candidate exists at every accessible world and has no
incoming selected ground from an existing concrete candidate at ANY admitted
world. Non-concrete explanations, uniqueness and divine attributes are not
excluded or supplied. -/
def NecessaryConcreteUnderivedAt (m : Profile W B) (w : W) : Prop :=
  ∃ b, m.concrete b ∧ m.ontic.ExistsAt w b ∧ NecessaryAt m.ontic w b ∧
    ∀ v a, m.concrete a → m.ontic.ExistsAt v a → ¬ m.grounds v a b

/-- Two complete alternative worlds: the root `false` exists in both, while
`true` exists only at the selected actual world `false`. -/
def witnessProfile : Profile Bool Bool where
  ontic := {
    frame := { access := fun _ _ => True }
    ExistsAt := fun w b => b = false ∨ w = false
    Causes := fun _ _ _ => False }
  concrete := fun _ => True
  grounds := fun w a b => a = false ∧ b = true ∧ w = false

/-- One joint model of all six nonlogical premises, with an actual contingent
concretum grounded in the necessary root. No metaphysical possibility claim. -/
def JointWitness : Prop :=
  InhabitedConcreteAt witnessProfile.ontic witnessProfile.concrete false ∧
  ActualGroundingWF witnessProfile false ∧
  EveryContingentGroundedAt witnessProfile false ∧
  ActualReflexive witnessProfile.ontic false ∧
  NoContingentConcreteSupport witnessProfile false ∧
  ConcreteNecessaryUnionWF witnessProfile false ∧
  ∃ b, witnessProfile.concrete b ∧
    TruthCore.German.Kant.CosmologicalInference.ContingentAt witnessProfile.ontic false b

end TruthCore.Causality.NecessaryConcreteUnderived
