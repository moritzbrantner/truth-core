import TruthCore.Causality.ConstitutiveNatureUniqueness
import TruthCore.Logic.Configuration

/-! A configuration-use adapter around the checked #715 bridge. No new
individuation, content or act semantics: the only new atom exposes actual
first-mover *witnesses* in the supplied predicates, not real-world actuality. -/
namespace TruthCore.Causality.ConstitutiveConfiguration
open TruthCore.Case.Catholicism

/-- Positive failure of uniqueness, rather than bare negation of a universal.
This supplies a nonempty candidate carrier and two distinct first-mover
witnesses in the selected interpretation; it is not empirical existence. -/
def DistinctFirstMoversExist {B R : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop) : Prop :=
  ∃ f g, IsFirstUnmovedMover Moved Moves f ∧
    IsFirstUnmovedMover Moved Moves g ∧ f ≠ g
end TruthCore.Causality.ConstitutiveConfiguration
