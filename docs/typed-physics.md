# Typed *Physics*: motion, mover and moved (#401, item 1)

Most *Physics* readings in the corpus take `Prop` atoms (`def X (P : Prop) : Prop := P`), so nothing can follow from them and they cannot follow from anything (audit B, #388). This note records the first typed batch: *Physics* III.3, VII.1 (the regress) and VIII.4-5, stated over the act/potency vocabulary of the *prima via* and #374. The Lean is in `TruthCore/Greek/Aristotle/Physics/Typed/Motion.lean`; the results are under `TruthCore/Results/Aristotle/Physics/Typed/`.

## Method

- Each typed reading is a new statement with its own claim. Where an older atom reading of the same sentence exists, the new claim is its sibling (`interpretation_of`). The older statements and their transcription results are unchanged (invariant 6).
- Shared predicates: `MovedIn`, `MovesIn`, `InPotency`, `InAct`, `MovesAsMoved`, as in `ActPotencyModel`. Added primitives, each with a definition record: `ByNature`/`ByForce` (`DEF-NATURAL-AND-FORCED-MOTION`), `SelfMovedIn` (`DEF-SELF-MOTION-ARISTOTLE`), `PassiveNaturalIn` (`DEF-PASSIVE-NATURAL-MOTION`), `MovesPerAccidensIn` (`DEF-PER-ACCIDENS-MOVER`), `IsLocal` (`DEF-LOCAL-BODILY-MOTION`), `MovesPrimarily` (`DEF-PRIMARY-MOVER`), `Touches` (`DEF-CONTACT-OR-CONTINUITY`), `ComposedOf`, `TraversesInfiniteInFiniteTime`. Nothing is defined in terms of the shared predicates, so no premise becomes analytic.
- Two new disambiguations: `DISAMB-SELF-MOTION` (Aristotle's self-mover is not `MovesIn x x r`) and `DISAMB-MOVED-BY-SOMETHING` (by something / by another / per accidens).
- Passages: *Physics* VIII.4 and VIII.5 were pinned as `ARIST-PHYS-VIII-4` and `ARIST-PHYS-VIII-5` in the existing First1K snapshot, materialized and read with III.1-3 and VII.1.

## Results (all Comparator-verified, zero axioms, with omission countermodels)

| Result | Premises | Conclusion |
|---|---|---|
| `ARIST-PHYS-III-1-3-NO-MOVER-MOVES-ITSELF` | III.1 analysis of being moved; III.3 motion in the moved (new); mover in act; no act and potency in one respect | no mover moves itself in its respect (new) |
| `ARIST-PHYS-VIII-4-EVERY-MOVED-PER-SE-OR-PER-ACCIDENS` | VIII.4 division natural/forced; natural self/passive; forced by another; self-motion has a mover; light/heavy by generator or remover | everything moved is moved by something, per se or per accidens |
| `ARIST-PHYS-VIII-4-EVERY-MOVED-HAS-A-PER-SE-MOVER` | the same, with the generator reading | `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` (*prima via*) |
| `ARIST-PHYS-VII-1-LOCAL-REGRESS-FROM-CONTACT` | contact of primary local movers; touching chain forms one; that one traverses an infinite motion in finite time; nothing does | no infinite chain of local moved movers |
| `ARIST-PHYS-VII-1-REGRESS-FROM-PER-SE-REGRESS` | second movers; no infinite per se series | the same restricted regress |
| `ARIST-PHYS-VIII-5-FIRST-MOVER-NOT-MOVED-BY-ANOTHER` | something is moved; everything moved has some mover; no infinite series of movers moved by another | a mover not moved by another cannot be lacking |
| `ARIST-PHYS-VIII-5-REGRESS-FROM-PER-SE-REGRESS` | III.3; second movers; no infinite per se series | VIII.5's regress premise |

## Findings

1. **VIII.4, read literally, does not give the *prima via*'s premise.** Its last step names two movers of the light and the heavy: the generator, or the remover of a hindrance, whom 255b24-27 calls a mover only per accidens. With that disjunction a light thing moved only by the remover has no per se mover (`literalReadingDoesNotGivePerSeMover`). Only the generator reading (`ARIST-PHYS-256A-GENERATOR-OR-REMOVER-B`) yields `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER`. Its open commitment is that the generator still moves the light thing while it rises; the text does not say so.
2. **The relocation changes the root frontier.** Because `ARIST-PHYS-VIII-4-EVERY-MOVED-HAS-A-PER-SE-MOVER` is a verified non-transcription result, the frontier now enters `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` through its five premises. The *prima via* routes go from 37-41 to 41-45 open premises: one Aquinas premise is replaced by five finer Aristotelian ones, one of them the generator reading. On the case's broad reading of *motus* (`DISAMB-MOTION`) those premises must hold of every reduction from potency to act, while Aristotle states them of physical motions. That scope gap is an objection to the premises, not an equivocation. If the owner prefers not to relocate the premise, the result can be withdrawn and the theorem kept as a fact; the VIII.4 cluster would then join the graph only through the literal result's premises and lose its link to the giant component.
3. **VII.1's regress is strictly weaker than the *prima via*'s.** The typed reading keeps audit B's restriction: local, bodily motion, primary movers, moved movers, and a separate contact premise. The *prima via*'s second-movers and per se regress premises entail it, and the converse fails even with the second-movers premise (`restrictedRegressIsWeaker`: with no local respects there is no local chain, but the per se series is infinite). So VII.1 cannot discharge `STMT-NO-INFINITE-PER-SE-MOVER-SERIES`; it is a weaker reading that survives.
4. **VIII.5's regress follows from the *prima via*'s, given III.3.** A mover moved by another is being moved (III.3), so the second-movers premise makes it a per se link. VIII.5's conclusion is weaker than the *prima via*'s: a first mover not moved by another may move itself (256a19-21).
5. **III.1 + III.3 exclude self-moving in the same respect.** With the *prima via*'s mover-in-act and non-simultaneity premises, III.1's analysis and III.3 give that no mover moves itself in the respect in which it moves. That is stronger than `STMT-NOTHING-MOVES-ITSELF-IN-SAME-RESPECT`, which assumes that the self-mover is being moved. It is compatible with VIII.4's self-movers (`DISAMB-SELF-MOTION`).

## Remaining gaps

- VII.1, 241b24-242a15: the chapter's own proof that everything moved is moved by something (case split on an internal source; dividing a per se mover; rest-dependence on a part) is not typed. The respect-free statement `STMT-EVERY-MOVED-THING-HAS-SOME-MOVER` is stated, not derived, here. Audit B noted that the older result covers only the per se branch.
- VIII.5, 256a4-13 (stick, hand and man; the first mover moves more) is the natural source for `STMT-SECOND-MOVERS-MOVE-ONLY-AS-MOVED`, and 256a19-21 (the first mover, if moved, moves itself) and 256b3-257a27 (per accidens moved movers; same-kind motion) are not yet read for claims.
- III.1, 201a19-27 (natural movers are moved; an unmoved mover exists) and III.2, 202a3-12 (contact movers are affected; the mover brings a form) keep their predicate-schema readings; using them for derivations needs an instantiation that is not circular. In particular, III.1's announcement of an unmoved mover must not be used as a premise for the *prima via*'s conclusion.
- "Infinite" in VII.1 (an infinite chain; an infinite motion) has no Aristotelian definition record yet (audit B's open `DISAMB-INFINITE-ARISTOTLE`, #216). `TraversesInfiniteInFiniteTime` is a primitive; it is not the divine `DEF-INFINITE`, and the stipulative `DEF-QUANTITATIVE-INFINITY` asks for a sourced account before it is used in a result.
- The older atom statements of these chapters stay singletons or small components: the inference graph has no edge to them. They are related to the typed readings only through sibling claims.
