import TruthCore.Teleonomy.Mechanisms

/-!
#251: the existing naturalistic-teleonomy rival, not a new Fifth Way.

Whole-worldview answer map and fidelity judgments: docs/teleonomy-comparison.md.
The worldview includes explicit unexplained cells and the open global thesis
STMT-NATURAL-ENDS-WITHOUT-DIRECTING-INTELLIGENCE-TELEONOMY. The finite fragment
below tests consistency of its mechanisms with the already encoded Fifth Way
alternative; it does not settle the truth or total explanatory adequacy of that
global thesis. No lack of coverage counts as a contradiction.
-/
namespace TruthCore.Comparison.Teleonomy
open TruthCore.Teleonomy

/-- Flat commitments for bind-check. The first two are concrete mechanism
models; the last reuses #179's teleonomy countermodel without changing its sense.
Scientific occurrence claims remain separate source claims, not axioms here. -/
def NaturalisticFragment : Prop :=
  SelectionCoverage selectionExample ∧ FeedbackCoverage ∧ UnguidedFinalityModel
end TruthCore.Comparison.Teleonomy
