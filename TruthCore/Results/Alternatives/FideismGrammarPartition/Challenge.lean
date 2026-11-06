import TruthCore.Alternatives.FideismGrammarCases
import TruthCore.Logic.ExcludedMiddle
namespace TruthCore.Results.Alternatives.FideismGrammarPartition
open TruthCore.Alternatives.FideismGrammarCases
open TruthCore.Logic

/-- Exhaustiveness of the grammar-fixing cases from excluded middle alone
(#1010): every cased practice lies in one of the three cells. No list of
theories of grammar enters. -/
theorem partition {Being : Type} (hEM : ExcludedMiddle) (C : CasedPractice Being) :
    GrammarCasesCover C := by
  sorry

/-- The cells are pairwise exclusive. -/
theorem cellsExclusive {Being : Type} (C : CasedPractice Being) :
    ¬ (C.AuthoritiesFixGrammar ∧ ¬ C.AuthoritiesFixGrammar) ∧
      ¬ ((¬ C.AuthoritiesFixGrammar ∧ C.UseFixesGrammar) ∧
          (¬ C.AuthoritiesFixGrammar ∧ ¬ C.UseFixesGrammar)) := by
  sorry

end TruthCore.Results.Alternatives.FideismGrammarPartition
