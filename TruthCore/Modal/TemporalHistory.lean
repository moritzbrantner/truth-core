import Mathlib.Order.Defs.PartialOrder
import TruthCore.German.Kant.CosmologicalInference

/-! A small history extension of existing modal ontology. Alternative worlds,
individuals and times remain distinct parameters. Coherence is an explicit
proposition, not a hidden proof field or a change to Ontic.ExistsAt.
-/
namespace TruthCore.Modal.TemporalHistory
open TruthCore.German.Kant.CosmologicalInference

structure History (World Being Time : Type) where
  ontic : Ontic World Being
  IsAt : World → Being → Time → Prop
  now : Time

/-- This profile interprets Ontic presence at a designated time, rather than
as existence at some time in the history. No causal or grounding bridge follows. -/
def CoherentAtNow (h : History W B T) : Prop :=
  ∀ w x, h.ontic.ExistsAt w x ↔ h.IsAt w x h.now

/-- Presence at every supplied time in one history. On the Int controls this
is two-sided temporal perpetuity, not timeless eternity or modal necessity. -/
def EverlastingAt (h : History W B T) (w : W) (x : B) : Prop :=
  ∀ t, h.IsAt w x t

/-- Presence at t and absence at every strictly earlier supplied time.
No claim about later persistence is included. The controls use Int's full
standard order; arbitrary preorders need not compare every pair of times. -/
def BeginsAt [Preorder T] (h : History W B T) (w : W) (x : B) (t : T) : Prop :=
  h.IsAt w x t ∧ ∀ s, s < t → ¬ h.IsAt w x s

end TruthCore.Modal.TemporalHistory
