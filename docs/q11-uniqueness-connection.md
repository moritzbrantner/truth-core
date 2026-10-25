# Q11 nature and individuation connection

`AQUINAS-ST-I-Q11-A3-GOD-ONE-FROM-NATURE` derives the existing
`STMT-GOD-IS-ONE` by the first proof of ST I q.11 a.3. It imports the existing
`IsGod`/`GodIsOne` vocabulary rather than introducing another God predicate.
It gives a distinct alternative to the maximum-in-being proof; it changes no
selected `root_route`, old Challenge, or global definition.

## Source and reading

The complete pinned Latin q.11 a.3 and q.3 a.3 were materialized and read,
with q.3 a.2 as context. Q.3 a.3 is an added article slice of the *existing*
q.3 snapshot, with the same revision and raw Git blob. No overlapping new
snapshot was created. The q.11 article's other two proofs remain distinct.

The proof isolates three sourced but undefended commitments:

| Statement | Reading and role |
| --- | --- |
| `STMT-Q11-INDIVIDUATING-BASIS-INCOMMUNICABLE` | Q.11's first proof says the basis by which a singular is **this** singular cannot be communicated to several. `suppositumOf` represents that individuating basis; its injectivity is an explicit premise. |
| `STMT-Q11-GOD-SUPPOSITUM-IS-NATURE` | Q.3 a.3 identifies God's suppositum and nature; q.11 expressly invokes this result. The attributed conclusion is read universally over proper God instances, and remains an open premise. The present argument does not supply q.3's further metaphysical demonstration. |
| `STMT-Q11-PROPER-GOD-INSTANCES-HAVE-COMMON-NATURE` | Q.11 contrasts being God with being **this** God, after the human/this-human example. The explicit shared-nature reading considers hypothetical proper God instances under the same divine nature, represented by `deity`. The universal equality is the stated interpretive commitment; it is not a definition of `IsGod` or the article's uniqueness conclusion. Equality of nature values is stronger than merely using one predicate or word of several beings; vocabulary alone does not establish it. |

`essenceOf` reuses the existing Thomistic nature/quiddity sense, not modal
Scott/Gödel essence. `suppositumOf` and `essenceOf` both take values in
`Principle` so their images can be compared; this does not equate the Lean
types `Being` and `Principle`. Neither map has hidden laws. The new
suppositum/nature and God-being/person disambiguations make their scopes
explicit. A quantified God here is a divine **being**, not a distinct
Trinitarian person. There is no person ontology or inference identifying
Father, Son and Spirit.

For God instances `g` and `h`, the proof constructs
`suppositumOf g = essenceOf g = deity = essenceOf h = suppositumOf h`.
Incommunicability then yields `g = h`. No excluded middle, maximality,
perfection, or nominal-definition converse is used in this local theorem.

## Omission controls

Each countermodel has `Being = Principle = Bool` and `IsGod := True`, so
there really are two distinct God instances in the local encoded test.
These are logical sensitivity models of the stated local inputs, not
source-faithful theological alternatives or models of the complete root.

| Omitted premise | Remaining maps | What fails |
| --- | --- | --- |
| Individuation | Both maps constantly `false`, `deity = false` | Equal bases need not identify individuals. |
| Suppositum/nature identity | `suppositumOf = id`, essence constantly `false`, `deity = false` | Injective individuals need not have their common nature as individuating basis. |
| Common nature | Both maps `id` | Individuated natures need not coincide. |

All other local premises hold in each respective model, while `GodIsOne`
fails. The frozen theorems and Comparator configurations check all three.
The original q.3/q.11 source commitments therefore remain meaningful
philosophical obligations rather than being made true by the vocabulary.

## Composition and exact premise comparison

`CATHOLICISM-STAGES-ONE-TWO-Q11-NATURE` retains the First Way's witness and
its identity with the Fourth Way's maximum. It imports the same
`PrimaVia.primaVia`, `QuartaVia.quartaVia`,
`MaximeEnsIsGodViaFullDescription.maximeEnsIsGodViaFullDescription`, and
`FirstMoverIsMaximeEns.firstMoverIsMaximeEns` results. It applies the existing
eight pointwise Stage2 results for simplicity, perfection, goodness,
immutability, eternity, infinity, intellect and will at that witness. Only
the ninth attribute uses the new `godIsOneFromNature` result. The existing
`ClassicalAttributesSuffice` bridge remains an input.

`CATHOLICISM-FROM-PRIMA-VIA-WITH-Q11-UNIQUENESS` imports that witness result
and the unchanged `Skeleton.catholicismSkeleton`; uniqueness transports the
attributes to every proper God instance. Revelation, Jesus' authority and
actual Resurrection, founding and identification of the Church, teaching
authority, and Creed proposal remain open. The historical end is still a
structural transcription and is not historical verification.

Compared with the earlier same-witness First-Way root theorem, the exact
listed hypothesis set removes `STMT-GOD-IS-MAXIMAL-IN-BEING` and adds the
three Q11 commitments above: **40 rather than 38 inputs**. The selected
root theorem derives two of that earlier theorem's inputs from efficient
regress and general excluded middle; the new alternative leaves those same
already-proved intermediates to the existing frontier expansion.

The three local principles and the old universal God-to-maximum premise are
incomparable **in isolation**, since the former constrain nature/individual
maps but not maximality and the latter constrains maximality but not those
maps. This does **not** make the full alternative route weaker. Its other
premises already yield a named maximum. Uniqueness then transports that
maximum's property to every God. The extra frozen, Comparator-checked lemma
`maximalityFromNamedMaximumAndUniqueness` proves exactly this conditional
recovery from an explicitly named maximal witness plus `GodIsOne`. It is a
comparison lemma, not a registered global corpus derivation closing
`STMT-GOD-IS-MAXIMAL-IN-BEING`. The old full context cannot impose the new
laws on otherwise free maps. There is no assumption-count reduction or
unconditional naming converse.

The actual selected frontier remains **37 open: 1 bare, 36 sourced**.
Selecting only this alternative root in memory, without changing repository
routes, gives **39 open: 1 bare, 38 sourced**. Its exact difference is the
old universal God-to-maximum commitment replaced by the three sourced Q11
commitments. No philosophical premise is declared true or closed merely
because this alternative omits it. Defending the nature and individuation
principles, and the other metaphysical and historical premises, remains work.

These selected-route counts are distinct from the aggregate argument graph.
At the db75e95 baseline the aggregate has 401 open premises (31 bare, 370
sourced); with this addition it has 404 (31 bare, 373 sourced). The three new
Q11 inputs are open in the aggregate but have no path through the unchanged
selected root route.
