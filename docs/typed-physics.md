# Typed *Physics*: motion, mover and moved (#401, item 1)

Most *Physics* readings in the corpus take `Prop` atoms (`def X (P : Prop) : Prop := P`), so nothing can follow from them and they cannot follow from anything (audit B, #388). This note records the first typed batch: *Physics* III.3, VII.1 (the regress) and VIII.4-5, stated over the act/potency vocabulary of the *prima via* and #374. The Lean is in `TruthCore/Greek/Aristotle/Physics/Typed/Motion.lean`; the results are under `TruthCore/Results/Aristotle/Physics/Typed/`.

## Method

- Each typed reading is a new statement with its own claim (`STMT-EVERY-MOVED-THING-HAS-SOME-MOVER` has two, from VII.1 and VIII.5). Where an older atom reading of the same sentence exists, the new claim is its sibling (`interpretation_of`). The older statements and their transcription results are unchanged (invariant 6).
- Scope: all these readings are about Aristotle's physical motion. VIII.4's division and its conclusions carry an explicit guard (`IsPhysicalRespect`, `DEF-PHYSICAL-RESPECT`: place, quality, quantity); its other readings are scoped by their antecedent primitives; the III.3 and VIII.5 readings carry no guard and are accepted only under a physical instantiation of `MovedIn`/`MovesIn` (`DISAMB-MOTION`). Commitments the text does not make are separate, unattributed premises with no claim: `STMT-PER-ACCIDENS-MOVED-PASSIVE-MOTION-HAS-PER-SE-MOVER`, `STMT-EVERY-REDUCTION-TO-ACT-IS-PHYSICAL-MOTION`, and the VIII.5 accessibility commitment `STMT-NO-INFINITE-SERIES-OF-MOVERS-MOVED-BY-ANOTHER`.
- Shared predicates: `MovedIn`, `MovesIn`, `InPotency`, `InAct`, `MovesAsMoved`, as in `ActPotencyModel`. Added primitives, each with a definition record: `ByNature`/`ByForce` (`DEF-NATURAL-AND-FORCED-MOTION`), `SelfMovedIn` (`DEF-SELF-MOTION-ARISTOTLE`), `PassiveNaturalIn` (`DEF-PASSIVE-NATURAL-MOTION`), `MovesPerAccidensIn` (`DEF-PER-ACCIDENS-MOVER`), `IsLocal` (`DEF-LOCAL-BODILY-MOTION`), `MovesPrimarily` (`DEF-PRIMARY-MOVER`), `Touches` (`DEF-CONTACT-OR-CONTINUITY`), `ComposedOf` (`DEF-ONE-MADE-OF-ALL`, stipulative), `TraversesInfiniteInFiniteTime` (`DEF-INFINITE-TRAVERSAL-IN-FINITE-TIME`, stipulative), `IsPhysicalRespect` (`DEF-PHYSICAL-RESPECT`). No primitive is defined in terms of the shared predicates, so no premise becomes analytic; only the link relations (`LocalMovedMoverLink`, `MovedByAnother`, `MoverMovedByAnotherLink`) are defined from them.
- Chains in the VII.1 readings are injective (infinitely many distinct members), so finite cycles are not excluded. VIII.5's source claim likewise prohibits infinitely many distinct movers (`STMT-NO-INFINITE-DISTINCT-MOVERS-MOVED-BY-ANOTHER`). The induction proof instead consumes the separate accessibility commitment (`Acc`), which has no source claim and also excludes cycles. A formalization convention does not source that extra strength.
- Two new disambiguations: `DISAMB-SELF-MOTION` (Aristotle's self-mover is not `MovesIn x x r`) and `DISAMB-MOVED-BY-SOMETHING` (by something / by another / per accidens).
- Passages: *Physics* VIII.4 and VIII.5 were pinned as `ARIST-PHYS-VIII-4` and `ARIST-PHYS-VIII-5` in the existing First1K snapshot, materialized and read with III.1-3 and VII.1.

## Results (all Comparator-verified, zero axioms, with omission countermodels)

| Result | Premises | Conclusion |
|---|---|---|
| `ARIST-PHYS-III-1-3-NO-MOVER-MOVES-ITSELF` | III.1 analysis of being moved; III.3 motion in the moved (new); mover in act; no act and potency in one respect | no mover moves itself in its respect (new) |
| `ARIST-PHYS-VIII-4-EVERY-MOVED-PER-SE-OR-PER-ACCIDENS` | VIII.4 division natural/forced (physical motion); natural self/passive; forced by another; self-motion has a mover; light/heavy by generator or remover | everything physically moved is moved by something, per se or per accidens |
| `ARIST-PHYS-VIII-4-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER` | the same five, plus the added premise that a light/heavy motion with a per accidens mover also has a per se mover | every physical motion has a per se mover |
| `ARIST-PHYS-VIII-4-SCOPE-BRIDGE-TO-PRIMA-VIA` (transcription) | the previous conclusion; the added scope premise that every reduction to act is a physical motion | `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` (*prima via*) |
| `ARIST-PHYS-VII-1-LOCAL-REGRESS-FROM-CONTACT` | contact of primary local movers; touching chain forms one; that one traverses an infinite motion in finite time; nothing does | no infinite chain of local moved movers |
| `ARIST-PHYS-VII-1-REGRESS-FROM-PER-SE-REGRESS` | second movers; no infinite per se series | the same restricted regress |
| `ARIST-PHYS-VIII-5-FIRST-MOVER-NOT-MOVED-BY-ANOTHER` | something is moved; everything moved has some mover; additional accessibility commitment for movers moved by another | a mover not moved by another cannot be lacking |
| `ARIST-PHYS-VIII-5-REGRESS-FROM-PER-SE-REGRESS` | III.3; second movers; no infinite per se series | additional accessibility commitment for the VIII.5 mover relation |

## Findings

1. **VIII.4, read literally, does not give a per se mover.** Its last step names two movers of the light and the heavy: the generator, or the remover of a hindrance, whom 255b24-27 calls a mover only per accidens. With that disjunction a light thing moved only by the remover has no per se mover (`literalReadingDoesNotGivePerSeMover`). A per se mover for every physical motion follows only with an added premise the text does not state, that such a motion with a per accidens mover also has a per se mover (the inclusive "or" admits a motion whose only mover is the per accidens remover; 254b33-255a1, which places such motion among things moved by another, bears on the premise but does not state it). That premise is unattributed and open (Codex P1 on #404).
2. **Scope: VIII.4 concerns physical motion, the root premise every reduction.** The VIII.4 readings are restricted to respects of physical motion and conclude `STMT-EVERY-PHYSICAL-MOTION-HAS-A-PER-SE-MOVER`. They reach `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-MOVER` only through the unattributed scope premise `STMT-EVERY-REDUCTION-TO-ACT-IS-PHYSICAL-MOTION`, in a result labelled as a transcription. That premise is false on the case's broad reading of *motus* if some reduction from potency to act (in understanding, in willing) is not a physical motion. Because the bridge is a transcription with an open premise, the root premise stays open; the route records what would be needed for it (owner decision on #404: keep the derivation; Codex P1 on #404).
3. **VII.1's regress is strictly weaker than the *prima via*'s.** The typed reading keeps audit B's restriction: local, bodily motion, primary movers, moved movers, and a separate contact premise. The *prima via*'s second-movers and per se regress premises entail it, and the converse fails even with the second-movers premise (`restrictedRegressIsWeaker`: with no local respects there is no local chain, but the per se series is infinite). So VII.1 cannot discharge `STMT-NO-INFINITE-PER-SE-MOVER-SERIES`; it is a weaker reading that survives.
4. **The additional VIII.5 accessibility commitment follows from the *prima via*'s, given III.3.** A mover moved by another is being moved (III.3), so the second-movers premise makes it a per se link. VIII.5's conclusion is weaker than the *prima via*'s: a first mover not moved by another may move itself (256a19-21).
5. **III.1 + III.3 exclude self-moving in the same respect.** With the *prima via*'s mover-in-act and non-simultaneity premises, III.1's analysis and III.3 give that no mover moves itself in the respect in which it moves. That is stronger than `STMT-NOTHING-MOVES-ITSELF-IN-SAME-RESPECT`, which assumes that the self-mover is being moved. It is compatible with VIII.4's self-movers only if a self-mover's mover is a part distinct from the whole, as Aristotle says (`DISAMB-SELF-MOTION`).

## Remaining gaps

- VII.1, 241b24-242a15: the chapter's own proof that everything moved is moved by something (case split on an internal source; dividing a per se mover; rest-dependence on a part) is not typed. The respect-free statement `STMT-EVERY-MOVED-THING-HAS-SOME-MOVER` is stated, not derived, here. Audit B noted that the older result covers only the per se branch.
- VIII.5, 256a4-13 (stick, hand and man; the first mover moves more) is the natural source for `STMT-SECOND-MOVERS-MOVE-ONLY-AS-MOVED`, and 256a19-21 (the first mover, if moved, moves itself) and 256b3-257a27 (per accidens moved movers; same-kind motion) are not yet read for claims.
- III.1, 201a19-27 (natural movers are moved; an unmoved mover exists) and III.2, 202a3-12 (contact movers are affected; the mover brings a form) keep their predicate-schema readings; using them for derivations needs an instantiation that is not circular. In particular, III.1's announcement of an unmoved mover must not be used as a premise for the *prima via*'s conclusion.
- "Infinite" in VII.1 (an infinite chain; an infinite motion) has no Aristotelian definition record yet (audit B's open `DISAMB-INFINITE-ARISTOTLE`, #216). `TraversesInfiniteInFiniteTime` is a primitive with the stipulative `DEF-INFINITE-TRAVERSAL-IN-FINITE-TIME`; it is not the divine `DEF-INFINITE`.
- The older atom statements of these chapters stay singletons or small components: the inference graph has no edge to them. They are related to the typed readings only through sibling claims.

## VIII.5 regress fidelity correction (#404)

The materialized `ARIST-PHYS-VIII-5` witness, 256a17–19, prohibits going to
infinity through movers moved by another. The revised claim
`ARIST-PHYS-256A17-NO-INFINITE-MOVED-BY-ANOTHER-A` now binds only
`STMT-NO-INFINITE-DISTINCT-MOVERS-MOVED-BY-ANOTHER`: no injective `Nat`-indexed
chain of `MoverMovedByAnotherLink`s. It does not assert accessibility.
The previous attribution of `Acc` is rejected: acknowledging extra strength in
a note did not supply source evidence for it. Finite mutual movers illustrate
the gap: no infinite injective sequence exists on a finite set, while a cycle
prevents accessibility. No inference from this weaker claim to accessibility
is recorded.

`STMT-NO-INFINITE-SERIES-OF-MOVERS-MOVED-BY-ANOTHER` keeps its existing identity
and Lean type as an additional, unattributed commitment. Both existing result
types and proofs remain fixed. The first-mover result consumes this commitment;
the per-se-regress transfer derives it only conditionally from the existing
prima-via premises and III.3. Neither result establishes the commitment from
the source claim. The remaining source research is recorded in the existing
typed-motion candidate: an independently supported cycle exclusion and
induction justification, and the narrower instrumental-series reading.

The intended and actual root-frontier effect of this correction is no change:
no root obligation is discharged, and no existing theorem premise is added or
removed. `frontier --routes` retains costs 28, 29, 33, 35, 36, 36, 37, 38;
`frontier --reaching-root` retains 44 open premises (3 bare, 41 sourced but
undefended). The split adds a source statement outside those root-frontier
leaves. Shared conventions resolved to source revision
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`.
