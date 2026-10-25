import TruthCore.English.OConnor.Metaethics
import TruthCore.English.VanRoojen.MoralCognitivism
import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaSecundae.Question94.Article4
import TruthCore.Metaethics.Questions

/-!
The moral-error comparison (#183, part of the emotivism refutation #181): three
shared questions and how emotivism, quasi-realism and Catholic natural law
answer them (owner principle on #143: complete theories, "unexplained" is
counted, no win by subtraction).

Only theories and consistency claims live in this namespace: `bind-check`
treats every `TruthCore.Comparison.*` definition as a theory bundle.

## Answer map

* **Q-MORAL-ERROR** (can someone be in error about a moral matter?).
  Emotivism (O'Connor: moral statements have no truth value at all): **no**.
  `EMOTIVISM-EXCLUDES-MORAL-ERROR` derives that no one errs about a moral
  sentence. Carnap drew the same consequence ("there could be no moral knowledge
  or error", SEP §2.2). Emotivism can only re-describe an apparent error as a
  change of attitude.
  Catholic: **yes**. The Germans erred about robbery
  (`AQUINAS-ST-I-II-Q94-A4-GERMANS-ERRED`, ST I-II q.94 a.4), and errors about
  the secondary precepts arise "as errors arise in speculative matters" (a.6).
  Quasi-realism: **yes, in the minimal sense** (SEP §1.1, §4.3).
  `QUASI-REALISM-ADMITS-MORAL-ERROR` shows its minimal truth is consistent with
  moral error, so the emotivism result does not reach it. Where it deviates
  from realism is in what makes the error an error (the grounding question);
  that is #185's deviation map.
* **Q-MORAL-DISAGREEMENT** (is a moral disagreement a contradiction?).
  Emotivism: **no**. `EMOTIVISM-EXCLUDES-GENUINE-MORAL-CONTRADICTION` derives
  this. Its replacement account is Stevenson's "disagreement in attitude", a
  conative clash (SEP §3.5), which is recorded as a claim.
  Catholic: **yes**, because moral sentences have a truth value (q.94 a.4).
  Quasi-realism: yes, minimally: its thin truth-aptness is all the definition
  of a genuine contradiction asks for.
* **Q-MORAL-PROGRESS** (is a change of moral view sometimes a correction?).
  Catholic: **yes**. The natural law was so corrupted in some hearts "that they
  thought good what is naturally evil, and such corruption needed correction"
  (q.94 a.5 ad 1), a claim without Lean. Emotivism: **unexplained, on the
  cognitive reading only**. If a genuine correction must replace acceptance of an
  untrue, truth-apt sentence, emotivism cannot have one, since it admits no moral
  error. That bridge is not a premise of any result here; it is the open
  statement `STMT-GENUINE-MORAL-CORRECTION-REPLACES-AN-UNTRUE-BELIEF`, without
  Lean (Codex P1 on #188). An emotivist account of improvement as change of
  attitude by better standards is not recorded, so it is not refuted either.
  Quasi-realism, minimally, can call it correction.
-/

namespace TruthCore.Comparison.MoralError

open TruthCore.English.OConnor
open TruthCore.English.VanRoojen
open TruthCore.Latin.Aquinas.SummaTheologiae
open TruthCore.Metaethics

/-- The shared signature of the moral-error questions. -/
structure Sig where
  Agent : Type
  Sentence : Type
  Moral : Sentence → Prop
  /-- Has a truth value, in the thin sense the questions use. -/
  TruthApt : Sentence → Prop
  /-- Has a robust (substantial) truth value. -/
  RobustlyTruthApt : Sentence → Prop
  Holds : Sentence → Prop
  Accepts : Agent → Sentence → Prop
  Rejects : Agent → Sentence → Prop

/-- Quasi-realism: moral sentences are minimally, not robustly, truth-apt
(SEP §1.1). -/
def QuasiRealist (s : Sig) : Prop :=
  QuasiRealistMinimalTruthAptReading s.Moral s.TruthApt s.RobustlyTruthApt

/-- Someone errs about some moral sentence. -/
def MoralErrorOccurs (s : Sig) : Prop :=
  SomeMoralError s.Accepts s.Moral s.TruthApt s.Holds

/-- Quasi-realism admits moral error: its minimal truth and an actual moral
error are jointly satisfiable. -/
def QuasiRealismAdmitsMoralError : Prop :=
  ∃ s : Sig, QuasiRealist s ∧ MoralErrorOccurs s

end TruthCore.Comparison.MoralError
