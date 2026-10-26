# Is being a genus? (issue #340, first batch)

The *quarta via* (ST I q.2 a.3) says that what is maximal "in aliquo genere" causes everything in that genus, and it applies this to being. Aristotle (*Metaphysics* III.3, 998b22-27) and Aquinas (ST I q.3 a.5) say that being is not a genus. This note records what the first batch established, which readings were rejected and why, and what remains open.

## Sources pinned and read

| Passage | Locator | Witness |
|---|---|---|
| `ARIST-MET-III-3` | *Metaphysics* III.3 (998a20-999a23) | Perseus `tlg0086.tlg025.perseus-grc2`, existing snapshot |
| `ARIST-MET-IV-2` | *Metaphysics* IV.2 | same snapshot |
| `AQUINAS-ST-I-Q3-A5` | ST I q.3 a.5 | SCTA TAca84, `TAca84-d1e61-Dd1e1139` |
| `AQUINAS-ST-I-Q13-A5` | ST I q.13 a.5 | SCTA TAca84, `TAca84-d1e113-Dd1e1221` |

## What is proved (Lean, no axioms)

- `ARIST-MET-998B-BEING-NOT-A-GENUS`: every genus has a differentia, every differentia is a being, and a genus is not said of its own differentiae. So being is not a genus in the strict sense. The proof is a three-step reductio over typed predication: terms, `IsGenus`, `DifferentiaOf` and essential predication `SaidOf`. Each premise has an omission countermodel.
- `AQUINAS-ST-I-Q3-A5-GOD-IN-NO-GENUS`: imports the Aristotle theorem. Whatever God were properly in would be a genus, and it would be being, so God is properly in no genus. Each Aquinas premise has an omission countermodel.
- `QUARTA-VIA-STRICT-GENUS-READING-FAILS` (countermodel): take "genus" in the genus principle strictly and add Aristotle's premises. The *quarta via* then does not reach a cause of being, even though the model has a real strict genus and the principle holds there.
- `QUARTA-VIA-BROAD-GENUS-COMPATIBLE-WITH-BEING-NOT-A-GENUS` (model): take "genus" broadly, as any perfection. Then the whole *quarta via* (premises and conclusion) and Aristotle's premises hold together.

The objection that being is not a genus is recorded as an `attacks` relation on `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS`. It succeeds only against the strict reading. The broad reading, which the corpus formalization already used, survives it. This does not make the premise true: it stays open.

## Readings chosen and rejected

- **"Genus" in the *quarta via* (`DISAMB-GENUS`).** The strict reading is rejected as Aquinas' meaning, for four reasons:
  1. the example, heat, is a quality and not a strict genus of hot things;
  2. the principle is applied to being, which Aquinas says is no genus;
  3. q.3 a.5 ad 2 gives grades of being by approach to God, without a common genus;
  4. Aristotle's 999a6-14 says there is no genus over things ordered as better and worse.

  The strict reading is kept only as a formal contrast (`MaximumInStrictGenusCausesAllInGenusReading`) and has no claim.
- **Predication of the differentia (`DISAMB-PREDICATION-OF-DIFFERENTIA`).** Both premises use essential predication. If "being is said of every differentia" held only as a true but non-essential attribution, the argument would equivocate. Aquinas' "extra essentiam generis" and "extra ens" read the two premises in the same sense.
- **καὶ εἶναι (998b23).** We read it as predicative ("each differentia is a being"), fixed by the conclusion at 998b26-27. The existential reading ("differentiae exist") is not used. The existence of a differentia is taken from Aquinas' "omne genus habet differentias".
- **The status of Book III.** 998b22-27 is one side of an aporia. The claims attribute the argument as stated there. Aquinas takes it as Aristotle's demonstration.
- **God-form of the q.3 a.5 premise.** "If God were in a genus, his genus would be being" is stated for God only. Generalizing it to every being whose esse is its essence would strengthen the sentence, so it was not done.

## Remaining obligations

1. **Order models (issue item 3).** Make the univocal reading a single homogeneous preorder on one domain. Make the analogical reading of attribution an order by relation to a primary analogate (q.3 a.5 ad 2, `STMT-BEING-MEASURED-BY-APPROACH-TO-GOD`). On each model, test `STMT-MAXIMUM-IN-GENUS-CAUSES-ALL-IN-GENUS`, `STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH` and `STMT-MAXIMUM-IN-BEING-IS-FIRST-BEING`. `MoreIn esse` is still a primitive comparative compatible with both senses (`DISAMB-BEING-UNIVOCITY`). This work should use Mathlib's order theory once #337 lands.
2. **The rest of ST I q.3 a.5.** Still to formalize: the first proof (a differentia stands to its genus as act to potency), the third proof (things in one genus differ in esse), and not being in a genus *per reductionem* as a principle (God is principle of all esse). The third proof would connect to `STMT-FIRST-UNMOVED-MOVER-IS-SIMPLE`.
3. **Composition onto the root path.** A first-mover version of `STMT-GOD-IN-NO-GENUS` would need the simplicity result plus a generalized and separately sourced esse-essence premise.
4. **Unformalized sourced commitments.** `STMT-NO-GENUS-OVER-PRIOR-AND-POSTERIOR`, `STMT-BEING-SAID-PROS-HEN`, `STMT-DIVINE-NAMES-ANALOGICAL` and `STMT-BEING-FIRST-ANALOGICAL-PREDICATE` are claims without Lean declarations. Whether ST I q.13 a.5 is analogy of attribution or of proportionality (Cajetan or Suárez) is not decided. Those authors are orientation only until pinned.
