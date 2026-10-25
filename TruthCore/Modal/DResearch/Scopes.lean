import TruthCore.Modal.DResearch.Witnesses
import TruthCore.Modal.DResearch.Language

namespace TruthCore.Modal.DResearch
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite (deadEnd)
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)

/-- Scope comparisons use the same frame and atomic valuation throughout.
The K sink witnesses why the general self-access conclusion needs seriality;
the two-cycle inside pocket is invisible to the fixed language. -/
def ScopeChecks : Prop :=
  (¬ Serial deadEnd.frame ∧ MC deadEnd.frame allPredicates () ∧
    ¬ deadEnd.frame.access () ()) ∧
  (¬ MC pocket.frame (expressible pocket.frame pocket.valuation) 0 ∧
    MC pocket.frame (expressible pocket.frame pocket.valuation) 1 ∧
    MC pocket.frame (expressible pocket.frame pocket.valuation) 2 ∧
    Dia pocket.frame (MC pocket.frame (expressible pocket.frame pocket.valuation)) 0 ∧
    Box pocket.frame (MC pocket.frame (expressible pocket.frame pocket.valuation)) 0) ∧
  (¬ MC fork.frame (expressible fork.frame fork.valuation) 0 ∧
    MC fork.frame (expressible fork.frame fork.valuation) 1 ∧
    MC fork.frame (expressible fork.frame fork.valuation) 2 ∧
    Dia fork.frame (MC fork.frame (expressible fork.frame fork.valuation)) 0 ∧
    Box fork.frame (MC fork.frame (expressible fork.frame fork.valuation)) 0)
end TruthCore.Modal.DResearch
