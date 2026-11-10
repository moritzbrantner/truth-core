module

public import TruthCore.Causality.OriginToleranceIdentity

@[expose] public section

namespace TruthCore.Results.Causality.OriginToleranceIdentity
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Causality.ToleranceOriginRival (ToleranceNonEuclideanAt)
open TruthCore.Causality.ToleranceOriginRival.Control (Origin tolerance)
open TruthCore.Causality.OriginToleranceIdentity
open TruthCore.Causality.OriginToleranceIdentity.Control

/-- Bridge: origin closeness that is a tolerance, access determined by origin
closeness, and one individual varied beyond tolerance across two successors of
`w` give the structural tolerance rival at `w`. -/
theorem originToleranceNonEuclidean {W B O : Type} (m : Ontic W B) (Concrete : B → Prop)
    (I : OriginInterface W B O) (w : W)
    (hNear : NearIsTolerance I) (hAccess : OriginDeterminesAccess m I)
    (hVaried : VariedOriginAt m Concrete I w) :
    ToleranceNonEuclideanAt m.frame w := by
  refine ⟨fun a => (hAccess a a).2 fun x _ _ => hNear.1 _, fun a b hab => ?_, ?_⟩
  · exact (hAccess b a).2 fun x hb ha => hNear.2 _ _ ((hAccess a b).1 hab x ha hb)
  · obtain ⟨x, _, _, a, b, ha, hb, hxa, hxb, hFar⟩ := hVaried
    exact ⟨a, b, ha, hb, fun hab => hFar ((hAccess a b).1 hab x hxa hxb)⟩

/-- The encoded origin-tolerance countermodel (faithful only to its encoded commitments) and the restored surrogate, by
case analysis. -/
theorem faithfulControls : Control.Certificate := by
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · intro o; cases o <;> simp [interface, tolerance]
  · intro o o'; cases o <;> cases o' <;> simp [interface, tolerance]
  · intro u v
    cases u <;> cases v <;>
      simp [faithful, far, exists', interface, originOf, tolerance, Bool.forall_bool]
  · intro u x _ hx o ho
    let wit : Bool → Origin → World
      | false, Origin.minus => World.aMinus
      | false, Origin.actual => World.actual
      | false, Origin.plus => World.plus
      | true, Origin.minus => World.bMinus
      | true, Origin.actual => World.actual
      | true, Origin.plus => World.bPlus
    refine ⟨wit x o, ?_⟩
    cases u <;> cases x <;> cases o <;>
      simp_all [wit, faithful, far, exists', interface, originOf, tolerance]
  · exact ⟨false, trivial, trivial, World.aMinus, World.plus, by simp [faithful, far],
      by simp [faithful, far], rfl, trivial, by simp [interface, originOf, tolerance]⟩
  · simp [TruthCore.Causality.NecessarilyUnderived.ActualReflexive, faithful, far]
  · intro v x t hp
    cases v <;> cases x <;> simp_all [faithful, isAt, exists']
  · intro v s t _ hEmpty
    exfalso
    cases v
    · exact hEmpty false trivial (by simp [faithful, isAt, exists'])
    · exact hEmpty true trivial (by simp [faithful, isAt, exists'])
    · exact hEmpty true trivial (by simp [faithful, isAt, exists'])
    · exact hEmpty true trivial (by simp [faithful, isAt, exists'])
    · exact hEmpty true trivial (by simp [faithful, isAt, exists'])
  · refine ⟨World.plus, by simp [faithful, far], 0, 1, Nat.zero_lt_one, ?_,
      false, trivial, ⟨trivial, World.bMinus, by simp [faithful, far], by simp [faithful, exists']⟩,
      by simp [faithful, isAt]⟩
    intro x _ hCont hx
    cases x
    · simp [faithful, isAt] at hx
    · obtain ⟨_, u, hu, hAbsent⟩ := hCont
      cases u <;> simp [faithful, far, exists'] at hu hAbsent
  · intro hE
    have h := hE World.aMinus World.plus (by simp [faithful, far]) (by simp [faithful, far])
    simp [faithful, far] at h
  · rintro ⟨c, _, _, hNec⟩
    cases c
    · simpa [faithful, exists'] using hNec World.bMinus (by simp [faithful, far])
    · simpa [faithful, exists'] using hNec World.aMinus (by simp [faithful, far])
  · intro o; cases o <;> simp [restoredInterface, tolerance]
  · intro o o'; cases o <;> cases o' <;> simp [restoredInterface, tolerance]
  · intro u v; simp [restored, restoredInterface]
  · intro u x _ _ o ho
    exact ⟨o, ho, trivial, rfl⟩
  · exact ⟨(), trivial, trivial, Origin.minus, Origin.plus, by simp [restored, tolerance],
      by simp [restored, tolerance], trivial, trivial, by simp [restoredInterface, tolerance]⟩
  · exact ⟨(), trivial, trivial, fun _ _ => trivial⟩

end TruthCore.Results.Causality.OriginToleranceIdentity
