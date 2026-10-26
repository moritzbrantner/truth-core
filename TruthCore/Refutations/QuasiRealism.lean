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
results named; the mind-independence and epistemology rows (#192) cite the SEP
entries "Moral Anti-Realism" (`SEP-MORAL-ANTI-REALISM`), "Metaethics"
(`SEP-METAETHICS`) and "Moral Epistemology" (`SEP-MORAL-EPISTEMOLOGY`).
Blackburn's own texts (1984, 1993, 1998) stay candidates (invariant 18).

| Question | Realism | Quasi-realism | Status |
|---|---|---|---|
| Q-MORAL-TRUTH-APTNESS (can a moral sentence be true or false?) | yes | yes, minimally (§1.1, §4.1.2) | matches; no particular moral verdict is recorded for either theory (Codex P1 on #189) |
| Q-MORAL-LANGUAGE-VALIDITY (#182) | valid | valid, constant meaning (§2.4, §2.5) | matches as far as equivocation goes (`EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY`); explaining validity is open (`EXPRESSIVIST-LOGIC-OF-ATTITUDES-COST`) |
| Q-MORAL-ERROR (#183) | yes | yes, minimally (§4.3) | matches (`QUASI-REALISM-ADMITS-MORAL-ERROR`) |
| Q-MORAL-DISAGREEMENT (#183) | contradiction | contradiction, minimally | matches |
| Q-ROBUST-TRUTH (is "true" more than minimal?) | robustly truth-apt (preamble) | not robustly truth-apt (§1.1) | **deviates** (`QUASI-REALISM-DEVIATES-ON-ROBUST-TRUTH`); deviation target (#190): the collapse premise forces realism's answer (`MINIMALISM-COLLAPSES-ROBUST-TRUTH-DEVIATION`), the anti-realist order of explanation sustains quasi-realism's (`ANTIREALIST-ORDER-SUSTAINS-ROBUST-TRUTH-DEVIATION`); open |
| Q-EXPLANATORY-ORDER (do moral truths explain moral thought and talk, or the reverse?) | the truths explain the talk (§5.2) | the talk explains the truths (§5.2, Dreier) | **deviates**; recorded as alternatives, open; it is what the robust-truth deviation rests on |
| Q-SUPERVENIENCE (why must moral judgments supervene on natural ones?) | — | respecting supervenience is a requirement of competence, from the purposes of moral talk, with "no further inference to a metaphysical conclusion" (§3.4, Blackburn) | recorded; not an answer to what makes a moral judgment true |
| Q-MORAL-GROUNDING (what makes a moral judgment true?) | — | no answer in the pinned witness: the explanatory-order and supervenience entries do not supply one (Codex P1 on #189) | not yet sourced |
| Q-MIND-INDEPENDENCE ("if we all approved of cruelty, it would still be wrong"), as a sentence (`DISAMB-MIND-INDEPENDENCE`) | yes: the entry lists it among "the moral realist's assertions" (Anti-Realism §3.1); that objectivism yields it is not formalized | the program aims to earn this talk (Anti-Realism §3.1); that its legitimacy is then judged from within one's attitudes (Metaethics §4) is the project's combination of two witnesses (`DEF-MIND-INDEPENDENCE-INTERNAL`) | **matches only if the program succeeds**, which no witness asserts; this is the mimicry the collapse lemma bears on (§3.1 raises the collapse challenge here) |
| Q-MIND-INDEPENDENCE, as objectivity (do moral facts exist and are they mind-independent?) | yes: robust realism is objectivist (Anti-Realism §3.3) | does not affirm it, on the entry's framing of quasi-realism as a noncognitivist program with "an anti-realist metaphysical stance" (§3.1): a noncognitivist is neither objectivist nor non-objectivist (§3.3); Blackburn's own label is projectivism | **deviates, conditional on that framing**; recorded from sourced claims, no result |
| Q-MORAL-EPISTEMOLOGY (how we know it; `DISAMB-MORAL-KNOWLEDGE`) | no sourced answer; the epistemology entry's own working sense (not attributed to realism) is that moral knowledge entails (roughly) justified true belief, a putative representation of moral reality (preamble) | no sourced answer; the entry reports an option an expressivist "may" take: justified attitudes, called "true" deflationarily, without representing moral reality, not called knowledge (preamble) | **candidate deviation**, conditional on two unsourced attributions: that these are realism's and quasi-realism's answers (candidate `QUASI-REALISM-MORAL-EPISTEMOLOGY-WITNESS`); no result |

The deviations cluster at the explanatory level, as the owner expected. §5.2
reports the collapse argument (creeping minimalism) in the same terms: if
minimalism carries the whole program, "success would leave us with no way to
distinguish plausible non-cognitivism from cognitivism". The quasi-realist
regroups by contrasting minimal with robust truth and belief. That is exactly
the robust-truth deviation, and Dreier's order of explanation is the
explanatory-order deviation, which the grounding question (#191) still has to
connect to. Neither is refuted here; each is a deviation target with no
`refutes` relation. The mind-independence question splits (#192): quasi-realism
aims to match realism on the counterfactual sentence and, on the entry's
framing, deviates on objectivity, so the aimed-for match on the sentence does
not by itself make it a mimic theory in the sense of the collapse lemma. The
epistemology row stays a candidate until both answers are attributed.

The robust-truth target (#190) is now reduced to one disputed premise. Both
sides share the minimalist sufficiency conditions (surface syntax and
disciplined use, §5.2) and Divers and Miller's finding that moral sentences
meet them. Add the collapse premise (no truth-aptness more robust than the
minimal), and realism's robust answer follows (the bound result); that
quasi-realism's answer is then inconsistent is the unbound lemma
`collapseExcludesQuasiRealistMinimalTruth`, which also needs a moral sentence. Add instead the explanatory bridge (robust moral truth actually
explains our thought and talk; an unattributed open premise, since Dreier as
reported says only that robust truth is suited to explanatory work), the
anti-realist order of explanation and the asymmetry of the two orders, and
quasi-realism's answer follows, so the collapse premise fails.
#191 now supplies the typed test `MORAL-DATA-DO-NOT-CHOOSE-EXPLANATORY-ORDER`:
use and semantic truth conditions are distinct explanation relata, and the
purposes-to-supervenience-competence explanation is a separate edge. Two
interpretations share literally the same q.94 error/needed-correction data and
an adopted q.48 privation-based evil/truth test, yet reverse the explanatory
order. Error and the evil premise follow in both. This proves independence
within that encoding only: the primitive explanation relation is not constrained
by an unencoded philosophical bridge. It does not show that quasi-realism
endorses Catholic truthmaking, that complete rival theories are compatible,
or that a grounding answer has been supplied. The missing bridge is queued as
`MORAL-DATA-TO-EXPLANATORY-ORDER-BRIDGE`. Need for correction is not an
accomplished improvement, and q.48 evil need not be moral evil.

Which side holds turns on the order of explanation, which is open. The data
the quasi-realist accepts do not by themselves require the robust answer
(countermodel `quasiRealistDataDoNotRequireRobustTruth`).
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

/-- The explanatory bridge: if a moral sentence is robustly truth-apt, its truth
conditions actually explain our thought and talk with it (`TruthExplainsTalk`).

Not attributed to the SEP entry. The entry reports only that robust
propositions and properties are *suited* to explanatory work, and that minimal
ones "will likely not be suited to do much" of it
(`RobustMoralTruthSuitedToExplainReading`, Dreier; the hedged remark about
minimal ones is not formalized). Something can be suited to
explaining without explaining, and the anti-realist argument needs actual
explanation, so this stronger premise is an open premise of the project
(Codex P1 on #230), not a source reading. -/
def RobustMoralTruthIsExplanatory {Sentence : Sort u}
    (Moral RobustlyTruthApt TruthExplainsTalk : Sentence → Prop) : Prop :=
  ∀ φ, Moral φ → RobustlyTruthApt φ → TruthExplainsTalk φ

/-- The two orders of explanation exclude each other for a moral sentence:
where our thought and talk with it explain its truth conditions
(`TalkExplainsTruth`), those truth conditions do not explain that thought and
talk (`TruthExplainsTalk`).

Not attributed to the SEP entry. It is the explicit premise that makes Dreier's
"order of explanation" a contrast: if both directions could hold of one moral
sentence, the criterion would not separate realism from anti-realism. It is an
open premise of the project, recorded for the robust-truth deviation target
(#190), not a source reading. -/
def ExplanatoryOrderAsymmetric {Sentence : Sort u}
    (Moral TalkExplainsTruth TruthExplainsTalk : Sentence → Prop) : Prop :=
  ∀ φ, Moral φ → TalkExplainsTruth φ → ¬ TruthExplainsTalk φ

end TruthCore.Refutations.QuasiRealism
