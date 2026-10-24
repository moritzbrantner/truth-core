import TruthCore.Logic.ExcludedMiddle
import TruthCore.Results.Logic.ExcludedMiddleIrrefutable.Solution
namespace TruthCore.Results.Logic.ExcludedMiddleIffDne
open TruthCore.Logic
open TruthCore.Results.Logic.ExcludedMiddleIrrefutable (excludedMiddleIrrefutable)
/-- Excluded middle is equivalent to double-negation elimination, proved
constructively from no premises. Neither side is proved; only that each yields
the other. The right-to-left direction composes
`LOGIC-EXCLUDED-MIDDLE-IRREFUTABLE`: double-negation elimination applied to the
irrefutable `¬¬(p ∨ ¬p)` gives `p ∨ ¬p`. -/
theorem excludedMiddleIffDoubleNegationElimination :
    ExcludedMiddleIffDoubleNegationElimination := by
  constructor
  · -- Excluded middle gives double-negation elimination: in the case ¬p,
    -- ¬¬p is contradicted.
    intro hEM p hNotNot
    cases hEM p with
    | inl hp => exact hp
    | inr hNotP => exact absurd hNotP hNotNot
  · -- Double-negation elimination gives excluded middle from its
    -- constructively proved double negation.
    intro hDNE p
    have hIrrefutable : ¬ ¬ (p ∨ ¬ p) := excludedMiddleIrrefutable p
    exact hDNE (p ∨ ¬ p) hIrrefutable
end TruthCore.Results.Logic.ExcludedMiddleIffDne
