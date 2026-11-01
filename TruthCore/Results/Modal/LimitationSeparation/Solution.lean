import TruthCore.Modal.LimitationSeparation

namespace TruthCore.Results.Modal.LimitationSeparation
open TruthCore.Modal.LimitationSeparation
open TruthCore.Modal.LimitationPossibility
open TruthCore.Isabelle.AFP.GoedelGod (Property Box)
open TruthCore.Logic (ExcludedMiddle)

/-- Same four classifier inputs give an accessible target exemplar OUTSIDE Q.
No frame law, source interpretation or property-admission premise is supplied. -/
theorem separate {W B : Type} (F : TruthCore.Modal.Frame W)
    (L : Property W B → W → Prop) (Q Phi : Property W B) (w : W)
    (hKnown : KnownLimitingAt L Q w) (hTarget : NonlimitingAt L Phi w)
    (hClosure : BackwardClosedAt F L w) (hEM : ExcludedMiddle) :
    PossiblyOutsideAt F Q Phi w := by
  rcases hEM (PossiblyOutsideAt F Q Phi w) with hWitness | hAbsent
  · exact hWitness
  · have hInclusion : Box F (fun v => ∀ c, Phi c v → Q c v) w := by
      intro v hwv c hc
      rcases hEM (Q c v) with hQ | hNotQ
      · exact hQ
      · exact (hAbsent ⟨v, hwv, c, hc, hNotQ⟩).elim
    exact (hTarget (hClosure Phi Q hInclusion hKnown)).elim

end TruthCore.Results.Modal.LimitationSeparation
