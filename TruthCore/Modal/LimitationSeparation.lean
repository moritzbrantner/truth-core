import TruthCore.Modal.LimitationPossibility

/-! Stronger analyst consequence of the EXISTING classifier inputs. No source
reading, property domain, classifier meaning or frame principle is added. -/
namespace TruthCore.Modal.LimitationSeparation
open TruthCore.Isabelle.AFP.GoedelGod (Property Dia)

/-- A SAME accessible exemplar has the target property but not the known
limiting property. This is stronger than target possibility alone. -/
def PossiblyOutsideAt {W B : Type} (F : Frame W)
    (Q Phi : Property W B) (w : W) : Prop :=
  Dia F (fun v => ∃ c, Phi c v ∧ ¬ Q c v) w

end TruthCore.Modal.LimitationSeparation
