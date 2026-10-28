/-!
Analytical reassembly variant of the Theseus puzzle, not a historical attribution.
Plutarch, Theseus 23.1 (Perrin translation, PLUTARCH-THESEUS-23-EN), reports
replacement and opposed identity verdicts, but neither reassembly nor a solution.

Stages are occurrences, not substances. A bearer assignment says which object
occurs at each stage. Its equality is ordinary numerical equality; stages need
not be equal when their bearers are. The two slots each retain their position;
a Bool records old/new component generation at that slot. This finite fixture
stipulates component identities and replacement history, not ship identity.
-/
namespace TruthCore.Mereology.TheseusIdentity

inductive Stage where
  | original | intermediate | continued | reassembled
  deriving DecidableEq

/-- Exact component inventory: first/second coordinate tracks its own slot's
old (false) or new (true) component. Same inventory is stronger than equal
shape or equal quantity, and is not defined as identity of the whole. -/
def contents : Stage → Bool × Bool
  | .original => (false, false)
  | .intermediate => (true, false)
  | .continued => (true, true)
  | .reassembled => (false, false)

/-- Numerical identity of the bearer survives both specified one-part
replacement steps. This is a contested bridge, not a definition of continuity. -/
def Gradual {B : Type} (bearer : Stage → B) : Prop :=
  bearer .original = bearer .intermediate ∧
  bearer .intermediate = bearer .continued

/-- In this fixture, equality of exact component inventories suffices for
numerical identity. It is not essential parthood (identity implies same parts). -/
def Material {B : Type} (bearer : Stage → B) : Prop :=
  ∀ s t, contents s = contents t → bearer s = bearer t

/-- The continued and reassembled occurrences at the final time have distinct
bearers. This is separately assumed; different stage names do not prove it. -/
def Distinct {B : Type} (bearer : Stage → B) : Prop :=
  bearer .continued ≠ bearer .reassembled

/-- Only original and reassembled stages share their entire inventory. -/
theorem material_iff {B : Type} (b : Stage → B) :
    Material b ↔ b .original = b .reassembled := by
  constructor
  · intro h; exact h _ _ rfl
  · intro h s t he
    cases s <;> cases t <;> first | exact rfl | exact h | exact h.symm | cases he

/-- General finite-chain propagation, independent of any material inventory.
No bound on the number of replacements repairs the incompatible bundle if
identity is preserved at every step. -/
theorem chain_identity {B : Type} (b : Nat → B) (n : Nat)
    (h : ∀ i, i < n → b i = b (i + 1)) : b 0 = b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : b 0 = b n := ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self n)))
    exact hn.trans (h n (Nat.lt_succ_self n))

theorem incompatible {B : Type} (b : Stage → B)
    (g : Gradual b) (m : Material b) : ¬ Distinct b := by
  intro d
  exact d ((g.1.trans g.2).symm.trans ((material_iff b).mp m))

/-- Exhaustive conditional fork requires only decidable bearer equality,
not classical excluded middle for arbitrary metaphysical propositions.
Branches need not be exclusive. -/
theorem fork {B : Type} [DecidableEq B] (b : Stage → B) :
    ¬ Gradual b ∨ ¬ Material b ∨ ¬ Distinct b := by
  by_cases h₁ : b .original = b .intermediate
  · by_cases h₂ : b .intermediate = b .continued
    · by_cases hm : b .original = b .reassembled
      · exact Or.inr (Or.inr (incompatible b ⟨h₁, h₂⟩ ((material_iff b).mpr hm)))
      · exact Or.inr (Or.inl (fun m => hm ((material_iff b).mp m)))
    · exact Or.inl (fun g => h₂ g.2)
  · exact Or.inl (fun g => h₁ g.1)

/-- History-first: all replacement stages have one bearer, reassembly another. -/
def history : Stage → Bool
  | .original => false
  | .intermediate => false
  | .continued => false
  | .reassembled => true

/-- Material-first: old inventory has one bearer, both changed inventories
another. This witness rejects persistence at the first replacement step. -/
def material : Stage → Bool
  | .original => false
  | .intermediate => true
  | .continued => true
  | .reassembled => false

/-- A nonseparation control: a single bearer occurs at every stage. Its rejection
of Distinct is explicit, not advertised as a physically adequate ship theory. -/
def collapsed : Stage → Bool := fun _ => false

/-- Exact fixture facts, general incompatibility and exhaustive decidable fork,
and each of the three pairwise-surviving profiles. Every profile has the same
component inventories and replacement history. No profile is asserted actual
or metaphysically possible; no root premise or identity bridge is discharged. -/
def Certificate : Prop :=
  contents .original = contents .reassembled ∧
  contents .original ≠ contents .continued ∧
  contents .original ≠ contents .intermediate ∧
  contents .intermediate ≠ contents .continued ∧
  (∀ (B : Type) (b : Stage → B), Gradual b → Material b → ¬ Distinct b) ∧
  (∀ (B : Type) [DecidableEq B] (b : Stage → B),
    ¬ Gradual b ∨ ¬ Material b ∨ ¬ Distinct b) ∧
  (Gradual history ∧ Distinct history ∧ ¬ Material history) ∧
  (Material material ∧ Distinct material ∧ ¬ Gradual material) ∧
  (Gradual collapsed ∧ Material collapsed ∧ ¬ Distinct collapsed) ∧
  (∀ (B : Type) (b : Nat → B) (n : Nat),
    (∀ i, i < n → b i = b (i + 1)) → b 0 = b n)

end TruthCore.Mereology.TheseusIdentity
