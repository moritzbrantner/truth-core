import TruthCore.Alternatives.Fideism

/-!
Wittgensteinian fideism as a complete rival worldview (#1010, owner request
2026-11-05): a theory of religious discourse that answers the shared questions
by relocating them inside the religious form of life. It is stated at full
strength from the pinned SEP witnesses (`SEP-FIDEISM`, `SEP-RELIGIOUS-LANGUAGE`),
in three variants kept apart:

* **WF-N**, the characterization (Nielsen 1967, as SEP *Fideism* §2.2.4
  reports it): religion is self-contained and governed by its own grammar,
  logically cut off from other aspects of life, self-referential, intelligible
  only to believers, and not open to criticism.
* **WF-P1**, early Phillips (1976, as SEP *Religious Language* §4.1 quotes him):
  religious belief is "the expression of a moral vision"; praise of God does not
  refer to "some object called God".
* **WF-P2**, late Phillips (1995) and religious minimalism: "God" may be said to
  refer and God's reality to be a fact, but what reference, object and existence
  amount to is shown only inside the religious context; "true" has several
  senses with different extensions (1976: 142; 1995: 149). Religious beliefs
  depend for their sense on non-religious features of life, but not generally
  as conclusions on their justification (SEP *Fideism* §2.2.4).

Only theories and consistency claims live in this namespace: `bind-check`
treats every `TruthCore.Comparison.*` definition as a theory bundle.

## Answer map

Each answer is labelled: *reported* (the pinned SEP entries report it as the
variant's position), *reconstruction* (unattributed, the comparison's own
filling-in of what the variant would answer), or **unexplained**.

* **Q-RELIGIOUS-LANGUAGE** (what does "God exists" say?). Catholic: a truth
  about a being really distinct from the world, knowable from created things by
  natural reason (*Dei Filius* ch. 1-2). WF-P1, reported: religious belief is
  "the expression of a moral vision" and praise of God does not refer to "some
  object called God"; Phillips's early writings question whether religious
  utterances are descriptive. Reconstruction: the name "God" applies to no
  being (`STMT-GOD-NAMES-NO-BEING-WF-P1`). WF-P2, reported: "God" may be said to
  refer and God's reality to be a fact, but what reference, object and
  existence amount to must be shown in the religious context.
* **Q-EXISTENCE / Q-ULTIMATE** (why is there anything; is there a first
  cause?). No variant's answer is reported by the witnesses. Reconstruction:
  WF-N, treating religion as cut off from shared reason, gives the cosmological
  question no religious answer that answers to shared reason. **Unexplained.**
* **Q-FIRST-MOVER, Q-ATTRIBUTES**. Reconstruction, not Phillips's reported
  position: if "God" names no being (`STMT-GOD-NAMES-NO-BEING-WF-P1`), the five
  ways' conclusions are not what worship is about; on WF-P2 their sense would
  first have to be shown in the religious use. **Unexplained.**
* **Q-TRUTH**: WF-P2, reported: multiple truth concepts with different
  extensions (Phillips) or a pluralist truth predicate (Putnam's minimalism).
* **Q-MORAL-GROUNDING**: WF-P1, reported: religious belief as the expression of
  a moral vision. Objective grounding outside the practice: **unexplained**.
* **Q-REVELATION, Q-JESUS-AND-CHURCH**. Reported for Wittgenstein's 1938
  lectures (student notes, SEP *Religious Language* §4.2): historical facts
  cited for religious belief are not treated as historical, empirical
  propositions. Reported for minimalism (same section): historical evidence can
  inform and modify religious judgement. WF-N, reconstruction: historical
  evidence is no reason for faith, so whether the resurrection occurred is
  **unexplained** as a factual question.
* **Q-CRITICISM** (can religion be criticized from outside?). WF-N, reported
  thesis (4): no. Phillips, reported: only "their conception" of criticism is
  denied (1981, 89-90, as quoted in SEP *Fideism* §2.2.4). Nielsen's charge,
  reported: the view insulates every form of life from reasonable criticism or
  defence (2000: 147, as quoted in SEP *Religious Language* §4.2).
-/

namespace TruthCore.Comparison.Fideism

open TruthCore.Alternatives.Fideism

/-- The fideist bundle WF-N on a practice: internal grammar and the sharp
descriptive thesis that religion is cut off from shared reason. -/
def WittgensteinianFideism (P : Practice) : Prop :=
  InternalGrammarReading P ∧ CutOffReading P

/-- The bundle by itself is consistent: some practice satisfies it. So the
defeat recorded in `WF-FAILS-AS-DESCRIPTION-OF-CATHOLIC-PRACTICE` does not
come from fideism being incoherent; it comes from the Catholic practice's own
rule. -/
def WittgensteinianFideismConsistent : Prop :=
  ∃ P : Practice, WittgensteinianFideism P

end TruthCore.Comparison.Fideism
