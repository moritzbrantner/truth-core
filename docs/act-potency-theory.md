# Act and potency as a typed theory (#352)

Issue #352 asks whether the act/potency premises that every root route shares can be derived from fewer, more basic sourced axioms. This note records what the first PR found and what remains. The Lean is in `TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/ActPotencyTheory.lean` (vocabulary and formal facts) and `TruthCore/Results/Aquinas/SummaTheologiae/ActPotencyModels.lean` (finite models).

## Sources read

- *Metaphysics* IX (Θ).1–9 are pinned as passages `ARIST-MET-IX-1` … `ARIST-MET-IX-9` (Perseus Greek, same snapshot as the other *Metaphysics* passages). Θ.1, Θ.3, Θ.6 and Θ.8 were materialized and read. Θ.2, Θ.4, Θ.5, Θ.7 and Θ.9 are pinned but not yet read for claims.
- *Physics* III.1–3 (`ARIST-PHYS-III-1` … `-3`, already pinned) were re-read for the act/potency readings.
- Aquinas, ST I q.2 a.3 co. (prima via) and I q.3 a.1 co. (second proof).

New source claims:

| Claim | Locator | Statement |
|---|---|---|
| `ARIST-PHYS-201A-ACT-POTENCY-NOT-SIMUL-A` | *Physics* III.1, 201a19-21 | `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT` (an Aristotelian witness for the existing premise) |
| `ARIST-MET-1049B-MOVER-ALREADY-ACTUAL-A` | *Met.* IX.8, 1049b26-27 | `STMT-NOTHING-MOVES-EXCEPT-AS-IN-ACT` (an Aristotelian witness for the existing premise) |
| `ARIST-MET-1049B-ACTUAL-BY-ACTUAL-A` | *Met.* IX.8, 1049b24-26 | `STMT-NOTHING-REDUCED-TO-ACT-EXCEPT-BY-A-BEING-IN-ACT` (new) |
| `AQUINAS-ST-I-Q2-A3-REDUCED-BY-A-BEING-IN-ACT-B` | ST I q.2 a.3 co. | same new statement; sibling of `-REDUCED-BY-A-MOVER-A` |
| `AQUINAS-ST-I-Q3-A1-REDUCED-ONLY-BY-BEING-IN-ACT-A` | ST I q.3 a.1 co. | same new statement (Aquinas' reason for simple priority) |
| `ARIST-MET-1048A-POTENCY-AS-UNACTUALIZED-CAPACITY-A` | *Met.* IX.6, 1048a30-35 | `STMT-POTENCY-IS-UNACTUALIZED-CAPACITY` (new; a definitional analysis) |
| `ARIST-PHYS-201A-MOVED-AS-POTENCY-ACTUALIZED-C` | *Physics* III.1, 201a10-11 | `STMT-BEING-MOVED-IS-ACTUALIZATION-OF-POTENCY` (new; a definitional analysis, sibling of `ARIST-PHYS-201A-CHANGE-A`) |

The `supports` relations added with them say how each bears on a target premise without stating it. They close nothing.

Rejected interpretation: reading Θ.8, 1049b24-26 as the universal claim that *every* mover is in act. The sentence says that what comes to be actual does so *by something* actual. The universal claim is the separate clause 1049b26-27 (`ARIST-MET-1049B-MOVER-ALREADY-ACTUAL-A`), so it is recorded as its own claim instead of being folded into the existential one.

## Findings

1. **The eight target premises are mutually independent** (`ACT-POTENCY-PREMISES-INDEPENDENT`). For each premise there is a finite model of the other seven, together with sensible motion and a well-founded per se series, in which it fails. So no target follows from the other seven. This is independence from the tested premises only; it does not show that a derivation needs new vocabulary. Further premises over the same predicates could suffice: for example, `InPotency x r → MovedIn x r` and `MovesIn y x r → PriorSimply y x`, together with `HasMover` and `MoverInAct`, entail `ActPrior`. Any added premise, over old or new vocabulary, is a new open premise that needs its own source.
2. **Definitional analyses are conservative, so defining a term discharges nothing** (`ACT-POTENCY-DEFINITIONAL-ANALYSES-CONSERVATIVE`). The case's own definition record of potency (`DEF-POTENCY`: "able to be r without being r actually") is the Θ.6 analysis. If it were the Lean definition of `InPotency`, `STMT-NOTHING-IN-ACT-AND-POTENCY-IN-SAME-RESPECT` would be analytic. But an ability predicate satisfying the analysis exists exactly when non-simultaneity holds, so the premise's openness would only move to the analysis's fidelity. The same holds for `MovedIn` and *Physics* III.1's definition of motion with respect to `STMT-NOTHING-MOVED-EXCEPT-AS-IN-POTENCY`. `InPotency` and `MovedIn` therefore stay parameters. An analysis says more than its premise only once its new primitive (`CanBe`, `ActualizedQuaPotential`) is constrained by further sourced axioms.
3. **The prima via needs less than it is given** (`AQUINAS-ST-I-Q2-A3-PRIMA-VIA-FROM-BEING-IN-ACT`). Read with its last words, *nisi per aliquod ens in actu* says that each moved thing has *some* mover in act. That replaces both "whatever is moved has a mover" and "every mover is in act" in the prima via: 6 premises instead of 7, and the new premise is strictly weaker than the two it replaces (`AQUINAS-ST-I-Q2-A3-BEING-IN-ACT-READING-FACTS`). Dropping any one of the six leaves a model without a mover moved by none. The proof composes the existing `PrimaVia.primaVia` on the relation "moves while in act".
4. **Aquinas' reason for simple priority does not yield it by itself** (`AQUINAS-ST-I-Q2-A3-BEING-IN-ACT-READING-FACTS`, last conjunct). Even with every prima via premise, the being-in-act principle allows a being in potency in a respect in which nothing is moved and nothing is in act. ST I q.3 a.1 needs a further step from "potency is reduced only by act" to "every potency has a prior being in act".

## Premise comparison

These results connect and relate statements; none discharges a target. `python3 scripts/corpus.py frontier --reaching-root` reports 37 open premises (1 bare, 36 sourced-undefended) before and after. The root route still uses `STMT-NOTHING-MOVES-EXCEPT-AS-IN-ACT` in its attribute steps (the first mover's own act), where the being-in-act reading does not help, so result 3 does not shrink the root's premise set.

## Second PR: goodness relocated onto ST I q.5 a.1

Sources read: ST I q.5 a.1 (whole article), q.4 a.1 (whole article), q.3 a.4 co. (second proof), and *Nicomachean Ethics* I.1 (new passage `ARIST-EN-I-1`, Perseus Greek).

5. **Goodness is actuality is derived from the article's own three steps** (`AQUINAS-ST-I-Q5-A1-GOODNESS-FROM-DESIRABILITY`, zero axioms). The steps are: the notion of good is the desirable (`STMT-GOOD-IS-DESIRABLE`); each thing is desirable insofar as it is perfect (`STMT-DESIRABLE-INSOFAR-AS-PERFECT`); each thing is perfect insofar as it is in act (`STMT-PERFECT-INSOFAR-AS-IN-ACT`, also q.4 a.1 co.). Each is read per perfection as a biconditional over four independent parameters (`GoodIn`, `DesirableIn`, `PerfectIn`, `Has`). The derived statement is exactly the existing `GoodnessIsActualityReading`. `premisesNeeded` gives an omission countermodel for each premise and a model of all three in which something is good.
   - **Definitional smuggling.** The first step is a *ratio* and could define `GoodIn` as `DesirableIn`. It is kept a premise. Were it a definition, the conclusion would be analytic relative to it, and the definition's fidelity would be the open premise.
   - **Fidelity.** The second step's stated reason (all things desire their own perfection) supports only the direction from perfect to desirable. The converse rests on reading *secundum quod* as a biconditional, the same reading the conclusion already has. The article's last clause (*esse est actualitas omnis rei*) is not used.
   - **Rejected.** Attributing the per-perfection biconditional to Aristotle. *EN* I.1 speaks of the ends of arts and actions, so its claim states its own statement and only `supports` the first step.
   - **Frontier.** This is a relocation, not a discharge: the target is now proved from three open sourced premises. Open root-path premises go from 52 to 54; route costs are unchanged.
6. **New witnesses, no derivation.** q.4 a.1 ad 2 (*oportet enim ante id quod est in potentia, esse aliquid actu*) is a third stating claim for act's simple priority, read as simple priority because the reply denies that the material principle is *simpliciter primum*. It gives the same reason as q.3 a.1, so it does not supply the missing step of finding 4. Its prior actual is the generator of the potential being (the animal before its seed), so it does not source `STMT-ACTUAL-MOVER-IS-SIMPLY-PRIOR` either. q.3 a.4 co. (*esse est actualitas omnis formae vel naturae*) is a second stating claim for actuality only insofar as being; it is not more basic (`ATTEMPT-Q4-A1-Q5-A1-ACT-PRIORITY-READING`).

## Remaining obligations for #352

- **(3) act simply prior to potency.** Source and formalize the missing step of finding 4: that every potency in a respect is related to some being in act in that respect that is simply prior to its bearer. Candidates: *Met.* Θ.8, 1049b17-29 (priority in time within a species) and 1050b3-6 (priority in substance), and Aquinas' commentary on Θ.8 (In Metaph. IX lect. 7-8, still unpinned). ST I q.4 a.1 ad 2 was read and does not supply the step (finding 6). This needs a reading of `PriorSimply` compatible with `DEF-SIMPLE-PRIORITY`.
- **(1) non-simultaneity.** A non-trivial derivation needs `CanBe` constrained independently, for example by Θ.3's anti-Megarian thesis (one can have an ability while not exercising it) or Θ.8, 1050b8-12 (every potency is a potency for both contradictories). Otherwise look for a sourced *per se nota* claim that would let the premise be marked self-evident.
- **(5) moves only as in act.** It is still needed for the first mover's own act in the attribute steps. A cheaper root route would have to derive those steps from the being-in-act reading, or show why they need the universal premise.
- **(4) goodness is actuality.** Relocated (finding 5). Closing it now needs its three premises closed; none has a recorded rival yet.
- **(2) actuality only insofar as being.** No more basic reading was found in Θ, ST I q.3 a.4, q.4 a.1 or q.5 a.1 (finding 6).
- **(6), (7), (8).** They now have Aristotelian supports (Θ.8; *Physics* III.1, III.3). (8), the per se premise, is outside act/potency proper and is better handled with the per se ordering work.
- Read Θ.2, Θ.4, Θ.5, Θ.7 and Θ.9 for further constraints on `CanBe`.
