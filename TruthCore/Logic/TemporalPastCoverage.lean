module

public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question2.Article3TertiaVia
public import TruthCore.Logic.ExcludedMiddle

/-! The existing first-time and pointwise-predecessor senses are logical
complements under excluded middle. The generic Before relation is unchanged;
no chronology, physical beginning, cardinal finiteness or infinite traversal
is inferred. A now parameter inhabits the time carrier. -/
@[expose] public section
namespace TruthCore.Logic.TemporalPastCoverage
open TruthCore.Latin.Aquinas.SummaTheologiae

def PastFork {T : Type} (Before : T → T → Prop) (now : T) : Prop :=
  PastIsInfinite Before now ∨ PastIsFinite Before now
end TruthCore.Logic.TemporalPastCoverage
