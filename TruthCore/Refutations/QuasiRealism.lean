import TruthCore.English.VanRoojen.MoralCognitivism

/-!
The quasi-realism deviation map (#185; owner method of 2026-10-24 on #181) and
its conclusion propositions. These live outside `TruthCore.Comparison` because
they are not theories: `bind-check` binds them to their statements by head
constant, without unfolding.

By the collapse lemma (`MIMIC-THEORY-COLLAPSES`), a theory that matches realism
on every shared question is no distinct rival and inherits realism's answer to
the grounding question. Quasi-realism (Blackburn, Gibbard) tries to earn
realism's answers. So the map records, question by question, whether its
answer **matches** realism or **deviates**. Sources are the SEP entry "Moral
Cognitivism vs. Non-Cognitivism" (`SEP-MORAL-COGNITIVISM`) and the earlier
results named.

| Question | Realism | Quasi-realism | Status |
|---|---|---|---|
| Q-MORAL-TRUTH-APTNESS (can a moral sentence be true or false?) | yes | yes, minimally (§1.1, §4.1.2) | matches; no particular moral verdict is recorded for either theory (Codex P1 on #189) |
| Q-MORAL-LANGUAGE-VALIDITY (#182) | valid | valid, constant meaning (§2.4, §2.5) | matches as far as equivocation goes (`EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY`); explaining validity is open (`EXPRESSIVIST-LOGIC-OF-ATTITUDES-COST`) |
| Q-MORAL-ERROR (#183) | yes | yes, minimally (§4.3) | matches (`QUASI-REALISM-ADMITS-MORAL-ERROR`) |
| Q-MORAL-DISAGREEMENT (#183) | contradiction | contradiction, minimally | matches |
| Q-ROBUST-TRUTH (is "true" more than minimal?) | robustly truth-apt (preamble) | not robustly truth-apt (§1.1) | **deviates** (`QUASI-REALISM-DEVIATES-ON-ROBUST-TRUTH`) |
| Q-EXPLANATORY-ORDER (do moral truths explain moral thought and talk, or the reverse?) | the truths explain the talk (§5.2) | the talk explains the truths (§5.2, Dreier) | **deviates**; recorded as alternatives, open |
| Q-SUPERVENIENCE (why must moral judgments supervene on natural ones?) | — | respecting supervenience is a requirement of competence, from the purposes of moral talk, with "no further inference to a metaphysical conclusion" (§3.4, Blackburn) | recorded; not an answer to what makes a moral judgment true |
| Q-MORAL-GROUNDING (what makes a moral judgment true?) | — | no answer in the pinned witness: the explanatory-order and supervenience entries do not supply one (Codex P1 on #189) | not yet sourced |
| Q-MIND-INDEPENDENCE ("if we all approved of cruelty, it would still be wrong") | yes | no answer in the pinned witness | not yet sourced |
| Q-MORAL-EPISTEMOLOGY (how we know it) | — | no answer in the pinned witness | not yet sourced |

The deviations cluster at the explanatory level, as the owner expected. §5.2
reports the collapse argument (creeping minimalism) in the same terms: if
minimalism carries the whole program, "success would leave us with no way to
distinguish plausible non-cognitivism from cognitivism". The quasi-realist
regroups by contrasting minimal with robust truth and belief. That is exactly
the robust-truth deviation, and Dreier's order of explanation is the
explanatory-order deviation, which the grounding question (#191) still has to
connect to. Neither is refuted here; each is a deviation target with no
`refutes` relation.
-/

namespace TruthCore.Refutations.QuasiRealism

open TruthCore.English.VanRoojen

universe u

/-- Quasi-realism's answer to `Q-ROBUST-TRUTH` (moral sentences are minimally,
not robustly, truth-apt) is not equivalent to realism's (they are robustly
truth-apt): the two theories do not match on that question. -/
def QuasiRealistRobustTruthAnswerDeviates {Sentence : Sort u}
    (Moral TruthApt RobustlyTruthApt : Sentence → Prop) : Prop :=
  ¬ (QuasiRealistMinimalTruthAptReading Moral TruthApt RobustlyTruthApt ↔
      RealistRobustTruthAptReading Moral RobustlyTruthApt)

end TruthCore.Refutations.QuasiRealism
