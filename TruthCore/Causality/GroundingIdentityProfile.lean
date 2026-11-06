module

public import TruthCore.Causality.BruteFoundationDoubling
public import TruthCore.Modal.CounterpartNecessity

/-!
Analyst reconstruction for #1078; attribution deferred. One LocalState is
represented twice on the SAME Bool × B candidate roster and universal frame.
The old doubled profile puts each world's existing individuals at its own tag;
the rigid companion keeps tag false at every world. Tags are rigid individual
coordinates, not time, qualitative features or a counterpart identity rule.
Grounding and cause edges merely copy the old source interpretation; their
metaphysical adequacy, identity, PSR and anti-brute principles remain OPEN.
The actual-world assignments agree literally. Neither rival is vindicated.
-/

@[expose] public section

namespace TruthCore.Causality.GroundingIdentityProfile
open BruteFoundationDoubling BruteFoundationBoundary
open TruthCore.German.Kant.CosmologicalInference
namespace CP := TruthCore.Modal.CounterpartNecessity

/-- Copy the old actual-world existence and edge assignments to every world.
The independent source concrete predicate and universal frame are retained. -/
def rigid (s : LocalState B) : Profile Bool (Bool × B) where
  ontic := {
    frame := (doubled s).ontic.frame
    ExistsAt := fun _ => (doubled s).ontic.ExistsAt false
    Causes := fun _ => (doubled s).ontic.Causes false
  }
  concrete := (doubled s).concrete
  grounds := fun _ => (doubled s).grounds false

/-- The precise local laws already preserved by the old doubling theorem.
Noninitial remains independently supplied on source coordinates. No new
existential dependence or unrestricted anti-brute-root premise is introduced. -/
def LocalLaws (m : Profile Bool (Bool × B)) (noninitial : B → Prop) : Prop :=
  (∀ w, InhabitedAt m w) ∧
  (∀ w, WellFounded (m.grounds w)) ∧
  (∀ w y x, m.grounds w y x →
    m.ontic.ExistsAt w y ∧ m.ontic.ExistsAt w x ∧ y ≠ x) ∧
  (∀ w x, m.concrete x → m.ontic.ExistsAt w x → noninitial x.2 →
    ∃ y, m.concrete y ∧ m.ontic.ExistsAt w y ∧ m.grounds w y x)

/-- Qualitative correspondence is equality of SOURCE coordinates, guarded
by existence in the appropriate domains. It is not equality of tagged beings.
This reuses the existing four-place counterpart-relation interface. -/
def counterparts (s : LocalState B) : CP.Relation Bool (Bool × B) :=
  fun w x v y => (doubled s).ontic.ExistsAt w x ∧
    (doubled s).ontic.ExistsAt v y ∧ x.2 = y.2

/-- Existence-preserving unique matching in both directions, with preservation
of concreteness and of the represented grounding/causing edges on existing
endpoints. No generic preservation of arbitrary modal formulas is asserted. -/
def SameLocalData (s : LocalState B) : Prop :=
  (∀ w x, (rigid s).ontic.ExistsAt w x →
    ∃! y, (doubled s).ontic.ExistsAt w y ∧ x.2 = y.2) ∧
  (∀ w y, (doubled s).ontic.ExistsAt w y →
    ∃! x, (rigid s).ontic.ExistsAt w x ∧ x.2 = y.2) ∧
  (∀ w x y, (rigid s).ontic.ExistsAt w x →
    (doubled s).ontic.ExistsAt w y → x.2 = y.2 →
    ((rigid s).concrete x ↔ (doubled s).concrete y)) ∧
  (∀ w a b x y, (rigid s).ontic.ExistsAt w a →
    (rigid s).ontic.ExistsAt w b → (doubled s).ontic.ExistsAt w x →
    (doubled s).ontic.ExistsAt w y → a.2 = x.2 → b.2 = y.2 →
    ((rigid s).grounds w a b ↔ (doubled s).grounds w x y) ∧
    ((rigid s).ontic.Causes w a b ↔ (doubled s).ontic.Causes w x y))

/-- One common-source comparison. Exact relational composition through ANY
intermediate world is stronger than merely having serial counterpart links.
Necessary existence on the rigid side is derived, not an input. -/
def Comparison (s : LocalState B) (noninitial : B → Prop) : Prop :=
  (rigid s).ontic.frame = (doubled s).ontic.frame ∧
  (rigid s).concrete = (doubled s).concrete ∧
  (rigid s).ontic.ExistsAt false = (doubled s).ontic.ExistsAt false ∧
  (rigid s).ontic.Causes false = (doubled s).ontic.Causes false ∧
  (rigid s).grounds false = (doubled s).grounds false ∧
  LocalLaws (rigid s) noninitial ∧ LocalLaws (doubled s) noninitial ∧
  SameLocalData s ∧
  CP.Total (doubled s).ontic (counterparts s) ∧
  CP.Unique (doubled s).ontic (counterparts s) ∧
  CP.Injective (doubled s).ontic (counterparts s) ∧
  (∀ w v y, (doubled s).ontic.ExistsAt v y →
    ∃ x, (doubled s).ontic.ExistsAt w x ∧ counterparts s w x v y) ∧
  (∀ w x, (doubled s).ontic.ExistsAt w x → counterparts s w x w x) ∧
  (∀ w v u x z,
    (∃ y, counterparts s w x v y ∧ counterparts s v y u z) ↔
      counterparts s w x u z) ∧
  (∀ b, s.existsAt b → CP.CounterpartNecessaryAt (doubled s).ontic
    (counterparts s) false (false, b)) ∧
  ¬ CP.IdentityBridge (counterparts s) ∧
  NecessaryConcreteAt (rigid s) false ∧ ¬ NecessaryConcreteAt (doubled s) false

/-- Closed conditional schema retains exactly the old source-side assumptions,
with a joint nonempty root-child instance and a genuine existing grounding
edge in both actual profiles. No metaphysical possibility or root discharge. -/
def Certificate : Prop :=
  (∀ (B : Type) (s : LocalState B) (noninitial : B → Prop),
    (∃ x, s.concrete x ∧ s.existsAt x) → WellFounded s.grounds →
    (∀ y x, s.grounds y x → s.existsAt y ∧ s.existsAt x ∧ y ≠ x) →
    NoninitialCovered s noninitial → Comparison s noninitial) ∧
  (Comparison exampleSource (fun x => x.2 = true) ∧
    (rigid exampleSource).grounds false (false, (false, false)) (false, (false, true)) ∧
    (doubled exampleSource).grounds false (false, (false, false)) (false, (false, true)))

end TruthCore.Causality.GroundingIdentityProfile
