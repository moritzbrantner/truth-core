module

public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Constructions
public import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.FinitePopulationCover
public import TruthCore.Logic.LimitAdmission
public import TruthCore.Logic.Configuration
public import TruthCore.Modal.S5Research
public import TruthCore.Models.PopulationClosureSeparation

/-! # Finite hitting sets (#561)
Analyst formulations; attribution deferred. Worlds are complete admissible
histories in one universal-accessibility component; `w` designates actuality.
The SAME candidate persists rigidly. Presence means concrete existence under
the stipulated interpretation, with no counterpart or temporal transition.
Compactness is Mathlib product-topological compactness, an OPEN modal policy.
No God, uniqueness, causal origin or actual applicability is established. -/

@[expose] public section
namespace TruthCore.Modal.FiniteHitting
open TruthCore.Case.Catholicism.StageOne.NecessaryIndividual
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)

/-- Universal accessibility on the supplied component, not all conceivable
worlds in other components. The explicit actual world witnesses nonemptiness. -/
def component (W : Type) : Frame W := ⟨fun _ _ => True⟩

/-- Negation of the existing de re predicate; the rigid roster is unchanged. -/
def NoNecessary {W I : Type} (F : Frame W) (p : ExistsAt W I) (w : W) : Prop :=
  ¬ DeRe F p w

/-- A finite list hits every population; other present individuals need not
belong to it. This differs from the EXISTING full population cover. -/
def Hitting {W I : Type} (p : ExistsAt W I) : Prop :=
  ∃ xs : List I, ∀ v, ∃ x ∈ xs, p x v

def OneFinite {W I : Type} (p : ExistsAt W I) : Prop :=
  ∃ v, Set.Finite {x | p x v}

/-- Existence cylinders in the product of discrete Bool spaces. The subtype
contains only admissible complete profiles; its frame is universal. -/
def profilePresent {I : Type} (S : Set (I → Bool)) : ExistsAt S I :=
  fun x v => v.val x = true

/-- All finite absences have a joint admissible witness; this does not supply
one witness for the entire possibly infinite roster. -/
def FiniteOmission {W I : Type} (p : ExistsAt W I) : Prop :=
  ∀ xs : List I, ∃ v, ∀ x ∈ xs, ¬ p x v

/-- Exact costs of the populated, amalgamating, no-necessary-individual rival.
World infinity means the actual component TYPE is infinite. -/
def Survivor {W I : Type} (p : ExistsAt W I) : Prop :=
  ¬ Hitting p ∧ (∀ v, Set.Infinite {x | p x v}) ∧ Infinite W ∧
  FiniteOmission p ∧ ¬ ∃ v, ∀ x, ¬ p x v

/-- Sufficient bridges A/B, finite component bound, and the rival's costs.
Classical logic is used explicitly by Mathlib, with its standard permitted axioms. -/
def Laws : Prop :=
  (∀ (W I : Type) (p : ExistsAt W I) (w : W),
    Hitting p → AbsenceAmalgamation (component W) p w → DeRe (component W) p w) ∧
  (∀ (W I : Type) (p : ExistsAt W I) (w : W),
    DeDicto (component W) p w → AbsenceAmalgamation (component W) p w →
    OneFinite p → Hitting p) ∧
  (∀ (W I : Type) (p : ExistsAt W I) (w : W),
    DeDicto (component W) p w → AbsenceAmalgamation (component W) p w →
    OneFinite p → DeRe (component W) p w) ∧
  (∀ (W I : Type) [Finite W] (p : ExistsAt W I) (w : W),
    DeDicto (component W) p w → AbsenceAmalgamation (component W) p w →
    DeRe (component W) p w) ∧
  (∀ (W I : Type) (p : ExistsAt W I) (w : W),
    DeDicto (component W) p w → AbsenceAmalgamation (component W) p w →
    ¬ DeRe (component W) p w → Survivor p)

/-- Genuine finite subcover theorem, then C and its noncompactness contrapositive.
No finite-character assumption is substituted for topological compactness. -/
def CompactLaws : Prop :=
  (∀ (I : Type) (S : Set (I → Bool)), IsCompact S →
    (∀ v : S, ∃ x, profilePresent S x v) → Hitting (profilePresent S)) ∧
  (∀ (I : Type) (S : Set (I → Bool)) (w : S), IsCompact S →
    DeDicto (component S) (profilePresent S) w →
    AbsenceAmalgamation (component S) (profilePresent S) w →
    DeRe (component S) (profilePresent S) w) ∧
  (∀ (I : Type) (S : Set (I → Bool)) (w : S),
    DeDicto (component S) (profilePresent S) w →
    AbsenceAmalgamation (component S) (profilePresent S) w →
    ¬ DeRe (component S) (profilePresent S) w → ¬ IsCompact S)

/-- Strict hierarchy controls use the existing world and presence types. -/
def finiteAndUnbounded : ExistsAt Bool ℕ := fun x v => v = true ∨ x = 0
def allInfinite : ExistsAt Bool ℕ := fun x v => v = false ∨ 1 ≤ x

def Weakening : Prop :=
  (DeDicto (component Bool) finiteAndUnbounded false ∧
    AbsenceAmalgamation (component Bool) finiteAndUnbounded false ∧
    OneFinite finiteAndUnbounded ∧ Hitting finiteAndUnbounded ∧
    ¬ FinitePopulationCover (component Bool) finiteAndUnbounded false) ∧
  (DeDicto (component Bool) allInfinite false ∧
    AbsenceAmalgamation (component Bool) allInfinite false ∧
    Hitting allInfinite ∧ ¬ OneFinite allInfinite) ∧
  (∀ (W I : Type) (p : ExistsAt W I) (w : W),
    FinitePopulationCover (component W) p w → OneFinite p)

/-- The strongest tail rival retains the OLD predicate, not a new ontology.
The topological noncompactness refers to its exact Boolean encoding from #486. -/
def TailBoundary : Prop :=
  FiniteCoverControls ∧
  DeDicto finiteCoverTailFrame finiteCoverTailPresent 0 ∧
  AbsenceAmalgamation finiteCoverTailFrame finiteCoverTailPresent 0 ∧
  ¬ DeRe finiteCoverTailFrame finiteCoverTailPresent 0 ∧
  Survivor finiteCoverTailPresent ∧
  ¬ IsCompact TruthCore.Logic.LimitAdmission.tailWorlds

/-- Empty, alternating and positive controls certify all single-premise deletions
of {H,A,¬N}, {P,A,O,¬N}, {P,A,K,¬N}; tail supplies H/O/K deletions. -/
def OmissionControls : Prop :=
  (∃ (I : Type) (S : Set (I → Bool)) (w : S), IsCompact S ∧
    AbsenceAmalgamation (component S) (profilePresent S) w ∧
    OneFinite (profilePresent S) ∧ ¬ DeDicto (component S) (profilePresent S) w ∧
    ¬ DeRe (component S) (profilePresent S) w) ∧
  (∃ (I : Type) (S : Set (I → Bool)) (w : S), IsCompact S ∧
    DeDicto (component S) (profilePresent S) w ∧ Hitting (profilePresent S) ∧
    OneFinite (profilePresent S) ∧ ¬ AbsenceAmalgamation (component S) (profilePresent S) w ∧
    ¬ DeRe (component S) (profilePresent S) w) ∧
  (∃ (I : Type) (S : Set (I → Bool)) (w : S), IsCompact S ∧
    DeDicto (component S) (profilePresent S) w ∧ Hitting (profilePresent S) ∧
    OneFinite (profilePresent S) ∧ AbsenceAmalgamation (component S) (profilePresent S) w ∧
    DeRe (component S) (profilePresent S) w)

/-- Explicit incompatible bundles; deletion controls certify inclusion-minimality
relative to this inhabited universal component, not global cardinal minimality. -/
def Cores : Prop :=
  (∀ (W I : Type) (p : ExistsAt W I) (w : W), Hitting p →
    AbsenceAmalgamation (component W) p w → ¬ DeRe (component W) p w → False) ∧
  (∀ (W I : Type) (p : ExistsAt W I) (w : W), DeDicto (component W) p w →
    AbsenceAmalgamation (component W) p w → OneFinite p →
    ¬ DeRe (component W) p w → False) ∧
  (∀ (I : Type) (S : Set (I → Bool)) (w : S),
    DeDicto (component S) (profilePresent S) w →
    AbsenceAmalgamation (component S) (profilePresent S) w → IsCompact S →
    ¬ DeRe (component S) (profilePresent S) w → False)

/-- The tail survivor in the SAME topological profile arena as theorem C. -/
def TailProfiles : Prop :=
  ∃ w : TruthCore.Logic.LimitAdmission.tailWorlds,
    DeDicto (component TruthCore.Logic.LimitAdmission.tailWorlds)
      (profilePresent TruthCore.Logic.LimitAdmission.tailWorlds) w ∧
    AbsenceAmalgamation (component TruthCore.Logic.LimitAdmission.tailWorlds)
      (profilePresent TruthCore.Logic.LimitAdmission.tailWorlds) w ∧
    ¬ DeRe (component TruthCore.Logic.LimitAdmission.tailWorlds)
      (profilePresent TruthCore.Logic.LimitAdmission.tailWorlds) w ∧
    Survivor (profilePresent TruthCore.Logic.LimitAdmission.tailWorlds) ∧
    ¬ IsCompact TruthCore.Logic.LimitAdmission.tailWorlds

/-- Full selected cluster. Earlier certified laws/controls are consumed unchanged. -/
def Package : Prop := FiniteCoverLaws ∧ Laws ∧ CompactLaws ∧ Weakening ∧
  TailBoundary ∧ OmissionControls ∧ TruthCore.Models.PopulationClosureSeparation.Separation ∧ Cores ∧ TailProfiles
end TruthCore.Modal.FiniteHitting
