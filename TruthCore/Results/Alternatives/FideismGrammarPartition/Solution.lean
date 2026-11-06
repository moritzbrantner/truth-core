module

public import TruthCore.Alternatives.FideismGrammarCases
public import TruthCore.Logic.ExcludedMiddle

@[expose] public section

namespace TruthCore.Results.Alternatives.FideismGrammarPartition
open TruthCore.Alternatives.FideismGrammarCases
open TruthCore.Logic

/-- Exhaustiveness of the grammar-fixing cases from excluded middle alone
(#1010): every cased practice lies in one of the three cells. No list of
theories of grammar enters. -/
theorem partition {Being : Type} (hEM : ExcludedMiddle) (C : CasedPractice Being) :
    GrammarCasesCover C := by
  rcases hEM C.AuthoritiesFixGrammar with hA | hA
  · exact Or.inl hA
  · rcases hEM C.UseFixesGrammar with hU | hU
    · exact Or.inr (Or.inl ⟨hA, hU⟩)
    · exact Or.inr (Or.inr ⟨hA, hU⟩)

/-- The cells are pairwise exclusive. -/
theorem cellsExclusive {Being : Type} (C : CasedPractice Being) :
    ¬ (C.AuthoritiesFixGrammar ∧ ¬ C.AuthoritiesFixGrammar) ∧
      ¬ ((¬ C.AuthoritiesFixGrammar ∧ C.UseFixesGrammar) ∧
          (¬ C.AuthoritiesFixGrammar ∧ ¬ C.UseFixesGrammar)) := by
  exact ⟨fun ⟨hA, hNotA⟩ => hNotA hA, fun ⟨⟨_, hU⟩, ⟨_, hNotU⟩⟩ => hNotU hU⟩

end TruthCore.Results.Alternatives.FideismGrammarPartition
