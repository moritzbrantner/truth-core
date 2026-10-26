import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3QuartaViaOrder
namespace TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaHomogeneousScale
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- The homogeneous scale of the model: both beings have being, and one is more a
being than the other exactly when it is above it in `Bool` (`false < true`). -/
theorem scale : HomogeneousScaleReading (fun (_ : Bool) (_ : Unit) => True)
    (fun _ x y => y < x) () :=
  ⟨fun _ => trivial, fun _ _ => Iff.rfl⟩

/-- On the univocal reading, the order gives no cause of being but leaves room
for one. On Mathlib's order of `Bool`, a homogeneous scale with greatest element
`true`: with no causation, the maximum causes nothing; with `true` causing the
being of `false`, the broad genus principle and *Metaphysics* II.1 both hold. -/
theorem homogeneousScaleGivesNoCauseOfBeing : HomogeneousScaleGivesNoCauseOfBeing := by
  refine ⟨?_, ?_⟩
  · -- INF-QUARTA-VIA-HOMOGENEOUS-SCALE-GIVES-NO-CAUSE-OF-BEING (1): nothing causes anything
    intro h
    have hMax : IsMaximumIn (fun (_ : Bool) (_ : Unit) => True) (fun _ x y => y < x) () true :=
      (scale.isMaximumIn_iff_isMax true).2 isMax_top
    exact h Bool Unit (fun _ _ => True) (fun _ x y => y < x) (fun _ _ _ => False) ()
      scale ⟨true, ⟨trivial, fun b _ => le_top⟩⟩ true hMax false (by decide) trivial
  · -- INF-QUARTA-VIA-HOMOGENEOUS-SCALE-GIVES-NO-CAUSE-OF-BEING (2): `true` causes the being of `false`
    refine ⟨Bool, inferInstance, Unit, fun _ _ => True, fun _ x y => y < x,
      fun c x _ => c = true ∧ x = false, (), scale, ?_, ?_, true,
      (scale.isMaximumIn_iff_isMax true).2 isMax_top⟩
    · intro r m hm x hx _
      cases m
      · exact absurd (show false < true by decide) (hm.2 true)
      · cases x
        · exact ⟨rfl, rfl⟩
        · exact absurd rfl hx
    · intro y x r _ hc
      obtain ⟨rfl, rfl⟩ := hc
      decide
end TruthCore.Results.Aquinas.SummaTheologiae.QuartaViaHomogeneousScale
