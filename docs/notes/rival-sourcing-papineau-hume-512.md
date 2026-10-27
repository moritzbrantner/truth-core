# Rival sourcing: Papineau and Hume against the 49 root-path premises (#512, #497)

This note records one reading pass over the two pinned rival-side sources. It
creates no worldview bundle and labels nobody's overall position. It reads single
passages into single claims, as the Aquinas claims do. Attempt record:
`ATTEMPT-RIVAL-SOURCING-PAPINEAU-HUME-512`.

## Sources read

All passages were materialized from their pinned witnesses and read in full:

- Papineau, "The Rise of Physicalism" (2001): `PAPINEAU-RISE-PHYSICALISM-3-12`
  (pp. 3–12) and the new `PAPINEAU-RISE-PHYSICALISM-13-33` (pp. 13–33, PDF
  pages 11–31, same snapshot bytes). The second passage covers the
  conservation-law history (Descartes, Leibniz, Newton, Helmholtz), vital and
  mental forces, and the conclusion that endorses the completeness of physics.
- Hume: `HUME-ENQUIRY-IV`, `HUME-ENQUIRY-V`, `HUME-ENQUIRY-VII` (with notes),
  `HUME-TREATISE-I-3-3`, `HUME-TREATISE-I-3-6`.

## Findings

Neither author states or denies any of the 49 premises in the case vocabulary.
Two readings bear on a premise and were recorded:

1. **Hume, *Treatise* I.3.6 §7.** "The same principle cannot be both the cause
   and effect of another." Claim `HUME-TREATISE-I-3-6-NO-MUTUAL-CAUSE-A`,
   statement `STMT-HUME-NO-MUTUAL-CAUSE` (non-modal, distinct relata). Result
   `HUME-NO-MUTUAL-CAUSE-FROM-NO-LOOPS`: `STMT-CAUSAL-HISTORY-HAS-NO-LOOPS`
   entails it. The converse fails for a self-cause and for a three-cycle on
   `Fin 3`. Hume therefore attests a strictly weaker consequence, not the premise.
2. **Papineau, p. 8, endorsed pp. 32–33.** The completeness of physics: all
   physical effects are fully determined by law by prior physical occurrences.
   Claim `PAPINEAU-RISE-COMPLETENESS-OF-PHYSICS-A`. Two explicit, unattributed
   bridges are added: `STMT-PHYSICAL-MOTION-IS-PHYSICAL-EFFECT` and
   `STMT-PRIOR-PHYSICAL-DETERMINATION-GIVES-MOVER`. With them it yields
   `STMT-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER` (result
   `PAPINEAU-COMPLETENESS-PHYSICAL-MOTION-MOVER`). That result is a
   single-application transcription, with `premisesNeeded` showing that all three
   premises are needed. The conclusion reaches
   `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` only through the existing
   scope result and its open scope premise. This is a conditional agreement on
   the mover premise for physical motion. Its weight rests on the second bridge,
   which reads a prior lawful determination (possibly by the body's own earlier
   state) as a present mover (`DISAMB-PRIOR-DETERMINATION-AND-MOVER`).

New senses: `DEF-PAPINEAU-PHYSICAL`, `DEF-PAPINEAU-LAWFUL-DETERMINATION`,
`DEF-HUME-CAUSE-EFFECT-RELATION`. New disambiguations: `DISAMB-PHYSICAL`
(Aristotle's respects of physical motion versus Papineau's physical as
non-special), `DISAMB-PRIOR-DETERMINATION-AND-MOVER`, and
`DISAMB-HUME-MAXIM-RELATION`.

## Per-premise table

P = Papineau, H = Hume. "Silent" means the texts neither state, deny nor
withhold the premise.

| Premise (STMT-…) | P | H | Note |
| --- | --- | --- | --- |
| CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH | silent | silent | Rejected: reading E IV §§9–11 ("the effect is totally different from the cause") as a denial. It is about a priori discoverability. |
| MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS | silent | silent | |
| MAXIMUM-IN-BEING-IS-FIRST-BEING | silent | silent | |
| POTENCY-IS-UNACTUALIZED-CAPACITY | silent | silent | Unknown "secret powers" mark an epistemic limit. E VII §27 and T I.3.6 §§8–10 keep "power" meaningful. |
| ACTUALITY-ONLY-INSOFAR-AS-BEING | silent | silent | |
| NO-COMPONENT-IS-FIRST-BEING | silent | silent | |
| CAUSE-OF-BEING-CAUSES-EVERY-PERFECTION | silent | silent | E VII §22 "nothing exists but by his will" reports the occasionalists. Hume does not assert it. |
| CAUSAL-FINITE-IMMEDIATE-PREDECESSORS | silent | silent | |
| CAUSAL-WELL-FOUNDED-PREDECESSORS | silent | silent | |
| CAUSAL-HISTORY-HAS-NO-LOOPS | silent | states a weaker consequence | Finding 1. |
| PER-SE-LINKS-IN-FINITE-HISTORY-RELATION | silent | silent | |
| NOTHING-MOVES-EXCEPT-AS-IN-ACT | silent | silent | |
| GOD-NAMES-THE-FULLY-DESCRIBED-PRINCIPLE | silent | silent | |
| PER-SE-MOVER-LINK-IS-PER-SE-CAUSE-LINK | silent | withholds (on occasionalism) | E VII §§24–25: "too bold"; "I cannot perceive any force in the arguments". Note D reports that Newton, Locke, Clarke and Cudworth grant second causes power. |
| AS-TO-BEING-SO-TO-TRUTH | silent | silent | |
| GRADES-HAVE-A-MAXIMUM | silent | silent | |
| THINGS-MORE-AND-LESS-GOOD-TRUE-NOBLE | silent | silent | P pp. 11–12 leaves noncausal realms of value open. |
| SECOND-MOVERS-MOVE-ONLY-AS-MOVED | silent | silent | E VII §14 and P p. 13 describe temporal chains, not a simultaneous per se series. |
| BEING-MOVED-IS-ACTUALIZATION-OF-POTENCY | silent | silent | |
| EVERY-MOTION-NATURAL-OR-FORCED | silent | silent | Neither uses the natural/forced division. |
| FORCED-MOTION-BY-ANOTHER | silent | silent | Rejected: reading note D ("continues for ever in its present state, till put from it by some new cause") as a denial. It denies only a *new* cause of continuing. It is not claimed; its conditional content parallels `NEWTON-PRINCIPIA-LEX-I-A`. |
| NATURAL-MOTION-SELF-OR-PASSIVE | silent | silent | |
| NATURAL-SELF-MOTION-HAS-A-MOVER | silent | silent | |
| PASSIVE-NATURAL-MOTION-BY-GENERATOR-OR-REMOVER | silent | silent | |
| PER-ACCIDENS-MOVED-PASSIVE-MOTION-HAS-PER-SE-MOVER | silent | silent | |
| GOD-IS-MAXIMAL-IN-BEING | silent | silent | |
| EVERY-CREATED-AGENT-ACTS-AS-APPLIED-TO-ACT-BY-GOD | silent | silent | Rejected: the conditional clash with P suggested on #512. The formal statement does not say that God is the mover. E VII §22 argues against occasionalism, which is compatible with concurrence. |
| ACT-SIMPLY-PRIOR-TO-POTENCY | silent | silent | |
| EVERY-REDUCTION-TO-ACT-IS-PHYSICAL-MOTION | silent | silent | Rejected: reading P's restricted physicalism as this scope premise (`DISAMB-PHYSICAL`). |
| SOMETHING-IS-MOVED-IN-THIS-WORLD | presupposes | presupposes | E VII §6, E IV §16 and P p. 13 take observed bodily motion for granted. Not claimed: this would need an appearance-to-reality step and the reading of local motion as a being moved. |
| NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER | conditional agreement (physical motion, via open bridges) | withholds demonstrability only | Finding 2; T I.3.3 (existing claims). |
| COMPOSITE-HAS-A-UNITING-CAUSE | silent | silent | |
| MATTER-FORM-AND-ESSE-ESSENCE-ARE-COMPOSITIONS | silent | silent | |
| GOODNESS-IS-ACTUALITY | silent | silent | |
| PERFECTIONS-OF-EFFECT-PREEXIST-IN-CAUSE | silent | silent | Rejected: reading E IV §11 ("every effect is a distinct event from its cause") as a denial. |
| IMMATERIAL-IS-INTELLECTUAL | silent | silent | Physicalism bears on the converse direction, not on this premise. |
| IMMUTABLE-IS-ETERNAL | silent | silent | |
| SUBSISTENT-BEING-IS-INFINITE | silent | silent | |
| WILL-FOLLOWS-INTELLECT | silent | silent | |
| CLASSICAL-ATTRIBUTES-SUFFICE | silent | silent | |
| Stage 3 (9 premises) | silent | silent | Enquiry X (miracles) would bear on PILOT-ROSE and REVELATION-POSSIBLE-AND-RECOGNIZABLE but is not pinned. |

## Remaining gaps

- Not claimed here, though genuine readings: Papineau's restricted physicalism and
  causal argument (pp. 9–12), and Hume's note D on inertia. Neither states nor
  denies a root premise. They become relevant atoms only once a root-path
  statement uses "physical" in Papineau's sense, or reads uniform motion as a
  being moved.
- Rival attestation still needs other texts: Enquiry X and XII, Dialogues IX,
  primary occasionalist texts (Malebranche, al-Ghazali), and an inertial reading
  of uniform motion as a being moved.
- Frontier effect: the Papineau result is an additional support route for
  `STMT-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER`. Its three premises are
  therefore listed by `frontier --reaching-root` (49 → 52). Every route's cost
  is unchanged.
