import TruthCore.Logic.Relativism
import TruthCore.Results.Logic.SelfApplication.Dilemma.Solution
namespace TruthCore.Results.Logic.Relativism.SelfFalsifying
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Relativism
/-- Horn 1 for "no absolute truth": if the thesis lies in its own scope and
disquotes, it is not absolutely true, so an absolute assertion of it commits
its speaker to a contradiction. Instance of the self-application dilemma with
absolute truth as acceptance and an unmeetable standard. -/
theorem thesisNotAbsolutelyTrue {Agent Content : Type} (T : TruthSemantics Agent Content)
    (scope : Content → Prop) (thesis : Content)
    (hScope : ThesisInOwnScope scope thesis) (hSays : ThesisDisquotes T scope thesis) :
    ThesisNotAbsolutelyTrue T thesis := by
  sorry
end TruthCore.Results.Logic.Relativism.SelfFalsifying
