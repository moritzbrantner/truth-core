module

public import TruthCore.Mereology.UniversalFusionBoundary
public import TruthCore.Mereology.ProcessTurnover
public import TruthCore.Mereology.TheseusIdentity

/-!
Analyst reconstruction of statue/lump coincidence; attribution deferred (#1075).
The fixture stipulates two times and one material token. The statue ceases after
reshaping while the lump persists. Those persistence judgments are framework
inputs, not conclusions about actual statues. One-object/sortal-relative rivals
may reject them. No modal or physical possibility is asserted.

Constituents are material tokens, not all mereological parts: in particular,
self-parts of different wholes must not be silently equated. Occurrence-set
extensionality compares entire histories; it supplies no slice-identity axiom.
The same represented observations do not identify the two ontologies.
-/

@[expose] public section

namespace TruthCore.Mereology.MaterialConstitutionScope

/-- Exact token coincidence at a represented time, with a nonempty slice.
This is neither equal mass/shape nor equality of all mereological parts. -/
def Coincident {T B M : Type} (material : T → B → M → Prop)
    (t : T) (x y : B) : Prop :=
  (∀ m, material t x m ↔ material t y m) ∧ ∃ m, material t x m

/-- Extra identity bridge under test. Temporal-whole extensionality has a
strictly different scope: all times, not any one nonempty slice. -/
def SliceIdentity {T B M : Type} (material : T → B → M → Prop) : Prop :=
  ∀ t x y, Coincident material t x y → x = y

/-- Divergent numerical persistence in one history, not across modal worlds. -/
def Divergent {T B : Type} (existsAt : T → B → Prop)
    (t : T) (x y : B) : Prop := ¬ existsAt t x ∧ existsAt t y

/-- false = initial time / statue label; true = later time / lump label.
Time and bearer have separate argument positions despite the finite Bool
encoding. Both exist initially; only the lump exists later. -/
def enduringExists (t b : Bool) : Prop := t = false ∨ b = true

def enduringMaterial (t b : Bool) (_ : Unit) : Prop := enduringExists t b

/-- Nonempty temporal wholes use Mathlib sets and subset parthood, as in
UniversalFusionBoundary.Body, but on time/token occurrences rather than Bool
material constituents. Reusing that concrete Bool carrier would erase time.
These are entire histories, not objects asserted wholly present at each time. -/
abbrev Whole := {s : Set (Bool × Unit) // s.Nonempty}

/-- Each enduring label is represented by its entire time/token history.
Nonemptiness is witnessed at the initial time for both labels. -/
def history (b : Bool) : Whole :=
  ⟨{o | enduringMaterial o.1 b o.2}, ⟨(false, ()), Or.inl rfl⟩⟩

def wholeExists (t : Bool) (x : Whole) : Prop := ∃ m, (t, m) ∈ x.val

def wholeMaterial (t : Bool) (x : Whole) (m : Unit) : Prop := (t, m) ∈ x.val

/-- The observations preserved by the correspondence are exactly existence
and each material token's membership at every represented time. No claim of
ontological equivalence or temporal parthood of enduring bearers is included. -/
def Correspondence : Prop :=
  (∀ t b, enduringExists t b ↔ wholeExists t (history b)) ∧
  (∀ t b m, enduringMaterial t b m ↔ wholeMaterial t (history b) m)

/-- A closed joint comparison. The first clause exposes the incompatible
bundle. The concrete clauses use ONE common history, including shared initial
material, divergent existence, overlapping but distinct temporal wholes, and
all-time observational correspondence. The universal extensionality clause
compares whole histories only. The last two clauses compose the previous
turnover boundary and finite-chain identity result; no root premise closes. -/
def Certificate : Prop :=
  (∀ (T B M : Type) (e : T → B → Prop) (c : T → B → M → Prop)
      (initial later : T) (x y : B),
    Coincident c initial x y → Divergent e later x y → ¬ SliceIdentity c) ∧
  (Coincident enduringMaterial false false true ∧
    Divergent enduringExists true false true ∧ false ≠ true ∧
    ¬ SliceIdentity enduringMaterial) ∧
  (Coincident wholeMaterial false (history false) (history true) ∧
    Divergent wholeExists true (history false) (history true) ∧
    history false ≠ history true ∧
    UniversalFusionBoundary.Overlap (history false) (history true) ∧
    ¬ (∀ p : Whole, p ≤ history false ↔ p ≤ history true)) ∧
  Correspondence ∧
  (∀ x y : Whole,
    (∀ t m, wholeMaterial t x m ↔ wholeMaterial t y m) → x = y) ∧
  ProcessTurnover.Boundary ∧
  (∀ (B : Type) (b : Nat → B) (e : B → Prop) (n : Nat),
    (∀ i, i < n → b i = b (i + 1)) → (e (b 0) ↔ e (b n)))

end TruthCore.Mereology.MaterialConstitutionScope
