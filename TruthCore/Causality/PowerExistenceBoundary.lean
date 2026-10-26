import TruthCore.Causality.EssentialPower
import TruthCore.German.Kant.CosmologicalInference

/-!
An analyst-defined separation for #319, not a source-derived metaphysical
claim. Finite grounding of *exercised power* and dependence of the *being*
which exercises it are different typed relations. Modal necessity and
composition introduce further independent conditions. No inference here
identifies a power source with God or with a simple first cause of esse.
-/
namespace TruthCore.Causality.PowerExistenceBoundary

open TruthCore.Causality
open TruthCore.German.Kant.CosmologicalInference

/-- A small common ontology for power transmission, direct support of esse,
and proper-part composition. The last three relations are not definitionally
interchangeable. -/
structure Profile (World Being : Type) where
  ontic : Ontic World Being
  transmitsPower : World → Being → Being → Prop
  supportsEsse : World → Being → Being → Prop
  intrinsicPower : World → Being → Prop
  properPartOf : Being → Being → Prop

/-- Power is original at this individual *in the chosen respect*: it has an
intrinsic power and receives no power through the designated transmission
relation. This does not assert existential self-sufficiency in every respect. -/
def UnborrowedPowerAt (m : Profile W B) (w : W) (x : B) : Prop :=
  m.ontic.ExistsAt w x ∧ m.intrinsicPower w x ∧
    ∀ y, ¬m.transmitsPower w y x

/-- Another existing being directly supports this individual's existence in
the selected world. This is distinct from transmission of a particular power. -/
def ExternallySupportedAt (m : Profile W B) (w : W) (x : B) : Prop :=
  ∃ y, m.ontic.ExistsAt w y ∧ y ≠ x ∧ m.supportsEsse w y x

/-- A proper component of the individual, without assuming that its
existence is sustained by that component or by an external cause. -/
def Composite (m : Profile W B) (x : B) : Prop :=
  ∃ y, y ≠ x ∧ m.properPartOf y x

/-- The represented relationships hold only between beings that exist at the
world. This blocks countermodels from relying on nonexistent power lenders or
existential supporters. Both kinds of efficient cause also count as causes in
the shared ontology. Components persist in both worlds of these models. -/
def Coherent (m : Profile W B) : Prop :=
  (∀ w y x, m.transmitsPower w y x →
      m.ontic.ExistsAt w y ∧ m.ontic.ExistsAt w x) ∧
  (∀ w y x, m.supportsEsse w y x →
      m.ontic.ExistsAt w y ∧ m.ontic.ExistsAt w x) ∧
  (∀ w y x, m.properPartOf y x →
      m.ontic.ExistsAt w y ∧ m.ontic.ExistsAt w x) ∧
  (∀ w y x, m.transmitsPower w y x → m.ontic.Causes w y x) ∧
  (∀ w y x, m.supportsEsse w y x → m.ontic.Causes w y x)

/-- Three distinct entities suffice: an original power source, its immediate
instrumental effect, and a potential conserver of the source's existence. -/
inductive Role where
  | source
  | effect
  | conserver
  deriving DecidableEq

/-- Two independent finite omission models:
1. A contingent original power source has an actual conserving cause of esse,
   even though the downstream effect's power is finitely grounded in it.
2. A modally necessary original power source has no recorded external
   conserver yet still has a proper component. Thus even adding necessary
   existence and the absence of an external conserver does not alone entail
   divine simplicity. These models refute bare *logical entailments*, not
   metaphysical premises about the relation of essence, esse and act. -/
def Boundary : Prop :=
  (∃ m : Profile Bool Role,
    (∀ w v, m.ontic.frame.access w v) ∧ Coherent m ∧
    UnborrowedPowerAt m false .source ∧
    FinitelyGroundedPower (m.transmitsPower false)
      (m.intrinsicPower false) .effect ∧
    ExternallySupportedAt m false .source ∧
    ContingentAt m.ontic false .source) ∧
  (∃ m : Profile Bool Role,
    (∀ w v, m.ontic.frame.access w v) ∧ Coherent m ∧
    UnborrowedPowerAt m false .source ∧
    FinitelyGroundedPower (m.transmitsPower false)
      (m.intrinsicPower false) .effect ∧
    (¬ExternallySupportedAt m false .source) ∧
    NecessaryAt m.ontic false .source ∧
    Composite m .source)

end TruthCore.Causality.PowerExistenceBoundary
