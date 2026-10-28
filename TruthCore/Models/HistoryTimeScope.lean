import TruthCore.Modal.TemporalHistory

/-! Formal quantifier controls on a shared timeline. These are analyst stipulations,
not definitions of metaphysical necessity or sourced readings of eternity. -/
namespace TruthCore.Models.HistoryTimeScope
open TruthCore.Modal.TemporalHistory

/-- Each supplied world has a possibly different witness time. -/
def Worldwise (h : History W B T) (x : B) : Prop := ∀ w, ∃ t, h.IsAt w x t
/-- One shared time witnesses presence in every supplied world. -/
def Common (h : History W B T) (x : B) : Prop := ∃ t, ∀ w, h.IsAt w x t
/-- Every world and every time; stronger than either existential-time scope. -/
def AllTime (h : History W B T) (x : B) : Prop := ∀ w t, h.IsAt w x t
/-- Within each world any presence propagates to every time. This is an explicit
additional restriction on IsAt, not a law of modal ontology or conservation. -/
def Uniform (h : History W B T) (x : B) : Prop :=
  ∀ w s t, h.IsAt w x s → h.IsAt w x t

/-- Two worlds, one candidate and two shared times. Ontic is deliberately
independent: no CoherentAtNow or existential-history coherence is assumed. -/
def diagonal : History Bool Unit Bool where
  ontic := { frame := { access := fun _ _ => True },
             ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  IsAt := fun w _ t => w = t
  now := false

/-- Both worlds share presence at false, and neither contains presence at true. -/
def synchronized : History Bool Unit Bool where
  ontic := diagonal.ontic
  IsAt := fun _ _ t => t = false
  now := false

/-- Exact quantifier hierarchy, two strictness controls, and an explicit
necessary-and-sufficient persistence restriction given worldwise presence.
AllTime is equivalent to Worldwise together with Uniform. This does not
identify Uniform with sourced eternity, changelessness or causal conservation. -/
def Controls : Prop :=
  (∀ (W B T : Type) (h : History W B T) (x : B),
    (AllTime h x → Common h x) ∧ (Common h x → Worldwise h x) ∧
    (AllTime h x ↔ Worldwise h x ∧ Uniform h x)) ∧
  (Worldwise diagonal () ∧ ¬ Common diagonal () ∧
    ∀ w, ¬ EverlastingAt diagonal w ()) ∧
  (Common synchronized () ∧ ¬ AllTime synchronized () ∧
    ∀ w, ¬ EverlastingAt synchronized w ())

end TruthCore.Models.HistoryTimeScope
