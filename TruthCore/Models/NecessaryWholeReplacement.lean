module

public import TruthCore.Models.NecessarilyUnderived
public import TruthCore.Causality.NecessaryConcreteUnderived

/-!
A fixed candidate with replaceable supporters, extending the existing switching
control. `none` is the same candidate at both worlds, NOT a certified mereological
whole: no parthood, fusion or real identity criterion is encoded. The support
interpretation is stipulated and not a metaphysical possibility claim. This tests
the root-route no-contingent-concrete-support bridge, not its negation in reality.
-/

@[expose] public section

namespace TruthCore.Models.NecessaryWholeReplacement

open TruthCore.Models.NecessarilyUnderived
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.NecessarilyUnderived
open TruthCore.Causality.NecessaryConcreteUnderived
open TruthCore.Causality.BruteFoundationBoundary

abbrev Candidate := Option Role

def present (w : Bool) : Candidate → Prop
  | none => True
  | some x => switchingExists w x

def support (w : Bool) : Candidate → Candidate → Prop
  | some a, some b => switchingSupport w a b
  | some a, none => (w = false ∧ a = .c) ∨ (w = true ∧ a = .d)
  | none, _ => False

def profile : Profile Bool Candidate where
  ontic := {
    frame := ⟨fun _ _ => True⟩
    ExistsAt := present
    Causes := fun _ _ _ => False }
  -- category-constant: intended (all-concrete inventory; this tests modal/support
  -- structure and supplies no independently warranted concreteness classification)
  concrete := fun _ => True
  grounds := support

def rank (w : Bool) : Candidate → Nat
  | none => 3
  | some a => switchingRank w a

/-- One joint structural interpretation. All admitted worlds are accessible;
all contingent candidates have present grounds at every world where they exist;
local support is well-founded, and no two opposite DIRECT edges occur even at
different worlds. The same necessary target receives contingent support at
every world. The necessary-only union is empty, and no necessary candidate is
underived at every world. No mereological or explanatory adequacy is asserted. -/
def Control : Prop :=
  NecessaryAt profile.ontic false none ∧
  profile.ontic.ExistsAt false none ∧
  (∀ w, ∃ a, profile.ontic.ExistsAt w a ∧ support w a none ∧
    ∃ v, ¬ profile.ontic.ExistsAt v a) ∧
  (∀ w a b, support w a b → present w a ∧ present w b) ∧
  (∀ w, WellFoundedPresentEsseSupport profile.ontic support w) ∧
  (∀ w, EveryContingentGroundedAt profile w) ∧
  (∀ v w a b, support v a b → ¬ support w b a) ∧
  (∀ a b, ¬ UnionNecessarySupport profile.ontic support false a b) ∧
  ConcreteNecessaryUnionWF profile false ∧
  ¬ NoContingentConcreteSupport profile false ∧
  ¬ NecessaryConcreteUnderivedAt profile false

end TruthCore.Models.NecessaryWholeReplacement
