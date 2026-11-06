module

public import TruthCore.Alternatives.FideismReference

/-!
Who fixes a practice's grammar: the cases (#1010; owner decision 2026-11-06).

The fideist's escapes from the two defeats of Wittgensteinian fideism
(`WF-FAILS-AS-DESCRIPTION-OF-CATHOLIC-PRACTICE`,
`FIDEIST-REFERENCE-BUNDLE-FAILS-FOR-CATHOLIC-PRACTICE`) turn on who fixes the
practice's grammar. The owner asks for both answers by cases, with the cases
partitioned by excluded middle (as for the F7 partition), not by a list.

Vocabulary (stipulative, `DEF-GRAMMAR-FIXED-BY-AUTHORITIES`,
`DEF-GRAMMAR-FIXED-BY-ORDINARY-USE`, `DEF-IN-ORDINARY-USE`):

* `AuthoritiesFixGrammar`: the practice's grammar is fixed by its recognized
  authorities (for the Catholic practice, the magisterium);
* `UseFixesGrammar`: it is fixed by its ordinary practitioners' use;
* `InOrdinaryUse m`: the move `m` belongs to the ordinary practitioners' use
  (what they are taught and profess).

The two `Prop` fields are constrained only through the case bridges below,
which connect them to the typed predicates of the practice. The third cell,
grammar fixed by neither (for instance by a philosopher's rational
reconstruction), is kept as its own case and is not defeated here.
-/

@[expose] public section

namespace TruthCore.Alternatives.FideismGrammarCases

open TruthCore.Alternatives.Fideism
open TruthCore.Alternatives.FideismReference

/-- A naming practice with the two grammar-fixing questions and ordinary use. -/
structure CasedPractice (Being : Type) extends NamingPractice Being where
  AuthoritiesFixGrammar : Prop
  UseFixesGrammar : Prop
  InOrdinaryUse : Move → Prop

variable {Being : Type}

/-- The three cells (`STMT-FIDEISM-GRAMMAR-CASES-COVER`): authorities fix the
grammar; or not, and ordinary use does; or neither does. -/
def GrammarCasesCover (C : CasedPractice Being) : Prop :=
  C.AuthoritiesFixGrammar ∨ (¬ C.AuthoritiesFixGrammar ∧ C.UseFixesGrammar) ∨
    (¬ C.AuthoritiesFixGrammar ∧ ¬ C.UseFixesGrammar)

/-- The third view (`STMT-GRAMMAR-FIXED-BY-NEITHER`), unattributed: the grammar
is fixed neither by the practice's authorities nor by its ordinary use. -/
def GrammarFixedByNeitherReading (C : CasedPractice Being) : Prop :=
  ¬ C.AuthoritiesFixGrammar ∧ ¬ C.UseFixesGrammar

/-- Case-1 bridge (`STMT-AUTHORITY-GRAMMAR-MAKES-DEFINITIONS-OWN-STANDARD`), open:
if the authorities fix the grammar, what a council defines is endorsed by the
practice's own standards. -/
def AuthorityCaseBridgeReading (C : CasedPractice Being) : Prop :=
  C.AuthoritiesFixGrammar → DefinitionIsOwnStandardReading C.toPractice

/-- Case-2 bridge (`STMT-USE-GRAMMAR-MAKES-ORDINARY-USE-OWN-STANDARD`), open: if
ordinary use fixes the grammar, what belongs to ordinary use is endorsed by the
practice's own standards. -/
def UseCaseBridgeReading (C : CasedPractice Being) : Prop :=
  C.UseFixesGrammar → ∀ m, C.InOrdinaryUse m → C.OwnStandard m

/-- Case-2 evidence (`STMT-ORDINARY-USE-AFFIRMS-NATURAL-KNOWABILITY`): some move of
ordinary use affirms that God can be known by the natural light of reason
(the catechesis ordinary believers receive; CCC 36 repeats Dei Filius, pinned in the official English translation). -/
def OrdinaryUseAffirmsNaturalKnowabilityReading (C : CasedPractice Being) : Prop :=
  ∃ m, C.AffirmsNaturalKnowability m ∧ C.InOrdinaryUse m

/-- Case-2 evidence (`STMT-ORDINARY-USE-CONFESSES-ONE-TRUE-GOD`): some move of
ordinary use confesses, with the name `god`, that there is a being it names
(the creed professed by believers; CCC 185-189, 199-200). -/
def OrdinaryUseConfessesGodReading (C : CasedPractice Being) (god : C.Name) : Prop :=
  ∃ m, C.ConfessesReferent m god ∧ C.InOrdinaryUse m

/-- Conclusion (`STMT-FIDEISM-FAILS-IN-AUTHORITY-AND-USE-CASES`): in the two
cells where the practice fixes its own grammar, both fideist bundles fail of
it: the cut-off pair and the reference bundle. Nothing about the third cell. -/
def FideismFailsInAuthorityAndUseCases (C : CasedPractice Being) (god : C.Name) : Prop :=
  C.AuthoritiesFixGrammar ∨ C.UseFixesGrammar →
    FideismFailsAsDescription C.toPractice ∧ FideistReferenceBundleFails C.toNamingPractice god

end TruthCore.Alternatives.FideismGrammarCases
