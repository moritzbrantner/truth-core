/-!
Wittgensteinian fideism as a rival account of religious discourse (#1010).

The position is recorded from two pinned secondary witnesses: the SEP entries
*Fideism* (Amesbury, §2.2.4) and *Religious Language* (Scott, §§1, 4.1, 4.2).
Phillips, Winch and Nielsen are in copyright and no legitimately hosted copy
was found, so their books carry bibliographic source identities only; no claim
here is read from them directly. Exegesis caution: the SEP entry doubts that
Wittgenstein endorsed any of the four theses usually called "Wittgensteinian
fideism"; nothing here attributes them to Wittgenstein.

## Vocabulary

A religious practice is viewed as a language game. `Practice` fixes its moves
(affirmations, condemnations, confessions made in it) and five predicates on
them; none carries a built-in philosophical premise:

* `Correct m`: `m` is a correct move by the grammar of the practice
  (`DEF-CORRECT-MOVE-IN-PRACTICE`);
* `OwnStandard m`: the practice's own authoritative standards endorse `m`
  (`DEF-PRACTICE-OWN-STANDARD`);
* `Defined m`: a council of the practice defines `m`, condemning its denial by
  canon (`DEF-CONCILIAR-DEFINITION`);
* `AffirmsNaturalKnowability m`: `m` affirms that God can be known with
  certainty from created things by the natural light of human reason;
* `AnswersToSharedReason m`: the correctness of `m` answers to standards of
  reason shared with those outside the practice
  (`DEF-NATURAL-REASON-SHARED`; contrasted in `DISAMB-NATURAL-REASON` with a
  practice-internal re-reading, `DEF-NATURAL-REASON-PRACTICE-INTERNAL`).

Not formalized here: early Phillips's thesis that God-talk does not refer to an
object (`STMT-PHILLIPS-GOD-TALK-NOT-REFERENCE-TO-AN-OBJECT`), recorded as a
rival of the nominal-definition leaves. Blocker: a typed reference relation for
"God" shared with those leaves.
-/

namespace TruthCore.Alternatives.Fideism

/-- A religious practice viewed as a language game: its moves and the five
predicates on them (see the module documentation). -/
structure Practice where
  Move : Type
  Correct : Move → Prop
  OwnStandard : Move → Prop
  Defined : Move → Prop
  AffirmsNaturalKnowability : Move → Prop
  AnswersToSharedReason : Move → Prop

/-- Fideist commitment 1, internal grammar (`STMT-WF-RELIGION-INTERNAL-GRAMMAR`):
whatever the practice's own standards endorse is a correct move in it.

SEP *Fideism* §2.2.4 reports the fideistic reading of Wittgenstein: religion
is "a self-contained and primarily expressive enterprise, governed by its own
internal logic or 'grammar'". SEP *Religious Language* §4.1 reports the
minimalist form: realism-relevant concepts are "language-game-internal", and
what makes for truth in religion is fixed by "the internal standards of
justification that inform religious discourse".

Weakest reading: only the direction from the practice's own standards to
correctness is used; that correctness is fixed *only* by them is not. -/
def InternalGrammarReading (P : Practice) : Prop :=
  ∀ m, P.OwnStandard m → P.Correct m

/-- Fideist commitment 2, the sharp descriptive thesis
(`STMT-WF-RELIGION-CUT-OFF-FROM-SHARED-REASON`): no correct move of the
religious practice is one whose correctness answers to standards of reason
shared with those outside it.

Reading of thesis (1) of the characterization reported in SEP *Fideism*
§2.2.4, "religion is logically cut off from other aspects of life", together
with (4), "religion cannot be criticized". It is the critics' characterization
(Nielsen's), which Phillips rejected as a caricature; Phillips's own later
view, that religious beliefs depend on non-religious features of life but not
"generally" as conclusions on their justification, is weaker and is recorded
separately (`STMT-PHILLIPS-RELIGION-NOT-GENERALLY-CONCLUSION`). -/
def CutOffReading (P : Practice) : Prop :=
  ∀ m, P.AnswersToSharedReason m → ¬ P.Correct m

/-- The practice's rule (`STMT-DEI-FILIUS-DEFINES-NATURAL-KNOWABILITY-OF-GOD`):
some defined move of the practice affirms that God can be known with
certainty from created things by the natural light of human reason.

Source: Vatican I, *Dei Filius* ch. 2 ("Eadem Sancta Mater Ecclesia tenet et
docet, Deum ... naturali humanae rationis lumine e rebus creatis certo
cognosci posse") and canon II.1 ("Si quis dixerit, Deum unum et verum ...
per ea, quae facta sunt, naturali rationis humanae lumine certo cognosci non
posse; anathema sit"). It is about knowability (posse), not about how
believers in fact come to believe. -/
def CouncilDefinesNaturalKnowabilityReading (P : Practice) : Prop :=
  ∃ m, P.AffirmsNaturalKnowability m ∧ P.Defined m

/-- Bridge (`STMT-CONCILIAR-DEFINITION-IS-PRACTICE-OWN-STANDARD`): in the
practice, what a council defines is endorsed by the practice's own standards.

Supported, not stated, by *Dei Filius* ch. 3 (what the Church proposes as
revealed by solemn judgment is to be believed with divine and catholic faith).
This is the bridge a fideist who keeps the internal-grammar thesis can still
reject, by treating conciliar teaching as theology about the practice rather
than as part of its grammar (`needsDefinitionIsOwnStandard`). -/
def DefinitionIsOwnStandardReading (P : Practice) : Prop :=
  ∀ m, P.Defined m → P.OwnStandard m

/-- Reading bridge (`STMT-NATURAL-REASON-IS-SHARED-REASON`): a move that affirms
God's knowability by the natural light of human reason answers to standards of
reason shared with those outside the practice.

Supported, not stated, by *Dei Filius* ch. 2, which sets this knowledge
"naturali humanae rationis lumine" against revelation "alia, eaque
supernaturali via". `DISAMB-NATURAL-REASON` records the rival,
practice-internal re-reading; `needsNaturalReasonIsShared` shows that under it
the fideist bundle survives. -/
def NaturalReasonIsSharedReading (P : Practice) : Prop :=
  ∀ m, P.AffirmsNaturalKnowability m → P.AnswersToSharedReason m

/-- Conclusion (`STMT-WF-FAILS-AS-DESCRIPTION-OF-PRACTICE`): the fideist pair
(internal grammar and the sharp descriptive thesis) does not hold of the
practice. Applied to the Catholic practice it says that Wittgensteinian
fideism, in the characterization's sharp form, misdescribes it. It says
nothing about other practices or about weaker fideist proposals. -/
def FideismFailsAsDescription (P : Practice) : Prop :=
  ¬ (InternalGrammarReading P ∧ CutOffReading P)

end TruthCore.Alternatives.Fideism
