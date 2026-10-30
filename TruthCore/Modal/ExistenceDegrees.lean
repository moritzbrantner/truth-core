import Mathlib.Order.Defs.PartialOrder
import TruthCore.Causality.NecessarilyUnderived

/-! A restricted modal existence-degree profile motivated by Koons's
2022-01-23 reconstruction, steps 6, 7 and 11. The pinned full content:encoded
item is KOONS-FOURTH-WAY-RECONSTRUCTION-2022-FULL-ITEM.

Existing Ontic supplies rigid candidate identity, a frame, world-relative
presence and actual causation. A new world-indexed degree assignment does not
define presence. All degree comparisons use one shared Mathlib Preorder.
The source allows a plurality of necessary beings. Selecting one N and giving
it a pointwise, other-directed possible-cause role is an explicit analyst
specialization, not an attribution of the full scope of source step 6.

The profile ranges only over worlds accessible from the selected standpoint.
No S5, causal soundness, sufficiency, value conversion or divine identity is
built in. Same degree is expressed by both order inequalities, not literal
identity of degree labels. -/
namespace TruthCore.Modal.ExistenceDegrees
open TruthCore.German.Kant.CosmologicalInference

variable {World Being Degree : Type}

/-- At v the same rigid x can cause the same rigid y: an actual causal edge
holds at some world accessible from v. This does not assert an edge at v. -/
def PossibleCauseAt (m : Ontic World Being) (v : World) (x y : Being) : Prop :=
  ∃ u, m.frame.access v u ∧ m.Causes u x y

/-- Analyst specialization of the source's possible universal causation: each
existing other individual has a causal-possibility witness, which may vary by
individual. It asserts neither self-causation nor one joint witness world.
The source's singular/plural and literal-all/other-directed alternatives are
not identified with this selected-individual profile. -/
def OtherDirectedPotentialCause (m : Ontic World Being) (w₀ : World)
    (n : Being) : Prop :=
  ∀ v, m.frame.access w₀ v → ∀ y, m.ExistsAt v y → y ≠ n → PossibleCauseAt m v n y

/-- Restricted reading of source step 7: among individuals existing at the
current evaluation world v, a possible cause has at least the recipient's
existence degree at v. The causal possibility is witnessed elsewhere; that
witness does not move the degree comparison to another evaluation world.
This is nonstrict and is not the stronger cause-is-more-such reading. -/
def WeakCauseDegreeBound [Preorder Degree] (m : Ontic World Being)
    (intensity : World → Being → Degree) (w₀ : World) : Prop :=
  ∀ v, m.frame.access w₀ v → ∀ x y,
    m.ExistsAt v x → m.ExistsAt v y → PossibleCauseAt m v x y →
      intensity v y ≤ intensity v x

/-- Analyst necessity-to-invariance condition. This bare NecessaryAt guard
can constrain the degree at an absent standpoint on a nonreflexive frame, so
it is not independently attributed to source step 11. The main theorem also
requires actual reflexivity. The separately named actual-presence-guarded
reading below preserves the source-fidelity boundary. An arbitrary named n
is not asserted necessary; equal degree means both inequalities, not label
identity or identification of intensity with presence. -/
def NecessaryDegreeInvariant [Preorder Degree] (m : Ontic World Being)
    (intensity : World → Being → Degree) (w₀ : World) (n : Being) : Prop :=
  NecessaryAt m w₀ n → ∀ v, m.frame.access w₀ v →
    intensity v n ≤ intensity w₀ n ∧ intensity w₀ n ≤ intensity v n

/-- Actual-presence-guarded selected-individual reading of source step 11.
The antecedent includes presence at the standpoint and presence at every
accessible world. This avoids constraining an absent individual's standpoint
degree merely because a nonreflexive frame makes NecessaryAt hold there. -/
def ActualNecessaryDegreeInvariant [Preorder Degree] (m : Ontic World Being)
    (intensity : World → Being → Degree) (w₀ : World) (n : Being) : Prop :=
  (m.ExistsAt w₀ n ∧ NecessaryAt m w₀ n) →
    ∀ v, m.frame.access w₀ v →
      intensity v n ≤ intensity w₀ n ∧ intensity w₀ n ≤ intensity v n

/-- The selected rigid n actually exists and exists at every root-accessible
world. At each such world its degree bounds all existing individuals' degrees
at all root-accessible worlds. The bound is attained by n at each world; ties
and other necessary individuals are allowed. No global metaphysical-world
scope beyond the chosen accessible family, value maximum or uniqueness follows.
Actual accessibility is an explicit theorem premise, not built into Ontic. -/
def NecessaryGlobalDegreeMaximum [Preorder Degree] (m : Ontic World Being)
    (intensity : World → Being → Degree) (w₀ : World) (n : Being) : Prop :=
  m.ExistsAt w₀ n ∧ NecessaryAt m w₀ n ∧
  ∀ v, m.frame.access w₀ v → ∀ u, m.frame.access w₀ u → ∀ y,
    m.ExistsAt u y → intensity u y ≤ intensity v n

/-- Some existing accessible-world pair attains an upper bound for all existing
accessible-world degree pairs. This auxiliary possible-maximum property does
not say that a particular n attains that bound at every world. -/
def AttainedGlobalDegreeMaximum [Preorder Degree] (m : Ontic World Being)
    (intensity : World → Being → Degree) (w₀ : World) : Prop :=
  ∃ v x, m.frame.access w₀ v ∧ m.ExistsAt v x ∧
    ∀ u, m.frame.access w₀ u → ∀ y, m.ExistsAt u y → intensity u y ≤ intensity v x

end TruthCore.Modal.ExistenceDegrees
