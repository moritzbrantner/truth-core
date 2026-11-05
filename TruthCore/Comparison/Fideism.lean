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

* **Q-RELIGIOUS-LANGUAGE** (what does "God exists" say?). Catholic: a truth
  about a being really distinct from the world, knowable from created things by
  natural reason (*Dei Filius* ch. 1-2). WF-P1: an expression of a moral vision
  and the grammar of worship, not a description. WF-P2: an assertion whose
  truth, reference and factuality are constituted inside the religious game.
* **Q-EXISTENCE / Q-ULTIMATE** (why is there anything; is there a first
  cause?). WF: the question, asked as a hypothesis about the world, is a
  confusion of grammars; asked inside the religious game, "God is the creator"
  expresses dependence and gratitude, not an explanatory hypothesis.
  As an answer to the cosmological question: **unexplained** (by design).
* **Q-FIRST-MOVER, Q-ATTRIBUTES**: WF denies that the five ways' conclusions
  are what believers mean by "God" (WF-P1) or holds that their sense must first
  be shown in the religious use (WF-P2): **unexplained**.
* **Q-TRUTH**: WF-P2, multiple truth concepts (Phillips) or a pluralist truth
  predicate (Putnam's minimalism); not truth as correspondence across games.
* **Q-MORAL-GROUNDING**: WF-P1, religion as moral vision; objective grounding
  outside the practice: **unexplained**.
* **Q-REVELATION, Q-JESUS-AND-CHURCH**: WF-N, historical evidence is not a
  reason for faith in the way evidence supports a hypothesis (SEP *Religious
  Language* §4.2 on Wittgenstein's 1938 lectures, student notes); WF-P2 and
  minimalism allow historical evidence to inform religious judgement (same
  section). Whether the resurrection occurred: **unexplained** as a factual
  question for WF-N.
* **Q-CRITICISM** (can religion be criticized from outside?). WF-N: no.
  Phillips: only "their conception" of criticism is denied (1981, 89-90, as
  quoted in SEP *Fideism* §2.2.4). Nielsen's charge: the view insulates every
  form of life from reasonable criticism or defence (2000: 147, as quoted in
  SEP *Religious Language* §4.2).
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
