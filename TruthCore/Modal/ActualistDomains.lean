import TruthCore.German.Kant.CosmologicalInference

/-! Guarded quantification over existing Ontic presence extensions. Predicate P
is arbitrary and TOTAL on the fixed candidate roster: absence does not make
P undefined or force it false. Only the quantifier is existence-guarded.
Domains vary as ExistsAt extensions, never as Lean identity or counterpart
rosters. No causal, temporal or nonempty-domain hypothesis is built in.
The two transfers concern this explicit profile, not every quantified logic. -/
namespace TruthCore.Modal.ActualistDomains
open TruthCore.German.Kant.CosmologicalInference
variable {W B : Type}

/-- All currently existing candidates satisfy the total supplied predicate. -/
def ActualistAll (m : Ontic W B) (P : W → B → Prop) (w : W) : Prop :=
  ∀ x, m.ExistsAt w x → P w x
/-- Existing membership persists along each accessibility edge. -/
def IncreasingDomains (m : Ontic W B) : Prop :=
  ∀ w v, m.frame.access w v → ∀ x, m.ExistsAt w x → m.ExistsAt v x
/-- Every successor member already belongs to the current domain. -/
def DecreasingDomains (m : Ontic W B) : Prop :=
  ∀ w v, m.frame.access w v → ∀ x, m.ExistsAt v x → m.ExistsAt w x
/-- Box of guarded forall entails guarded forall of box, for every total P. -/
def BoxAllToAllBox (m : Ontic W B) : Prop :=
  ∀ (P : W → B → Prop) w,
    (∀ v, m.frame.access w v → ActualistAll m P v) →
    ∀ x, m.ExistsAt w x → ∀ v, m.frame.access w v → P v x
/-- Guarded forall of box entails box of guarded forall, for every total P. -/
def AllBoxToBoxAll (m : Ontic W B) : Prop :=
  ∀ (P : W → B → Prop) w,
    (∀ x, m.ExistsAt w x → ∀ v, m.frame.access w v → P v x) →
    ∀ v, m.frame.access w v → ActualistAll m P v

end TruthCore.Modal.ActualistDomains
