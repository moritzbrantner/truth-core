import TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.Quantifiers

/-! Task-local cardinality diagnostics for #606. The fixed roster, literal
identity, accessibility and existence predicate retain Quantifiers' meanings.
All profiles here are stipulated interpretations, not sourced modal claims. -/
namespace TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission
open TruthCore.Modal
open TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1 (ExistsAt)

/-- Every indexed selection of at most k roster members can be omitted at one
accessible world. Repeated selections are allowed, so this covers sets with
at most k members without requiring a second set/cardinality vocabulary.
The n=0 clause requires an accessible world even for an empty roster. -/
def UpTo {W I : Type} (F : Frame W) (present : ExistsAt W I) (w : W)
    (k : Nat) : Prop :=
  ∀ n, n ≤ k → ∀ selection : Fin n → I,
    ∃ v, F.access w v ∧ ∀ i, ¬ present (selection i) v

/-- Three rigid roster members/world labels; an enumerated carrier avoids
importing cardinality or set machinery for this finite witness. -/
inductive Slot where
  | a | b | c
  deriving DecidableEq

/-- The universal frame with one inhabitant at each of three worlds. -/
def singletonFrame : Frame Slot := ⟨fun _ _ => True⟩

/-- World v contains exactly roster member v. This reuses the alternating
model's equality assignment on a three-member carrier, rather than changing
identity or the shared quantifier engine. -/
def singletonExists : ExistsAt Slot Slot := fun x v => x = v

/-- The advertised finite strictness witnesses plus the general structural
laws. Zero omission is successor existence, not a guarantee of population.
The Bool witness separates bound 1 from 2; the three-singleton witness separates
2 from 3 while remaining populated, with no fixed necessary individual and
no whole-roster absence. No unrestricted recombination principle follows. -/
def Hierarchy : Prop :=
  (∀ (W I : Type) (F : Frame W) (present : ExistsAt W I) w,
    UpTo F present w 0 ↔ ∃ v, F.access w v) ∧
  (∀ (W I : Type) (F : Frame W) (present : ExistsAt W I) w k l,
    k ≤ l → UpTo F present w l → UpTo F present w k) ∧
  (∀ (W I : Type) (F : Frame W) (present : ExistsAt W I) w k,
    JointAbsence F present w → UpTo F present w k) ∧
  (UpTo alternatingFrame alternatingExists false 1 ∧
    ¬ UpTo alternatingFrame alternatingExists false 2) ∧
  (Reflexive singletonFrame ∧
    UpTo singletonFrame singletonExists Slot.a 2 ∧
    ¬ UpTo singletonFrame singletonExists Slot.a 3 ∧
    IndividualContingency singletonFrame singletonExists Slot.a ∧
    DeDicto singletonFrame singletonExists Slot.a ∧
    ¬ DeRe singletonFrame singletonExists Slot.a ∧
    ¬ JointAbsence singletonFrame singletonExists Slot.a)

end TruthCore.Case.Catholicism.StageOne.NecessaryIndividual.BoundedOmission
