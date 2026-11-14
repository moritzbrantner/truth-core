# Potency and privation: support and exact bridges

Date: 2026-11-13. Evidence baseline:
`03d97b48a86d4b7d7bbedcb4441398ce3a9dadef`.

## Question and finding

This investigation concerns two of the nine common inputs in the
[terminal-only God-existence calculation](god-existence-support-formula.md#nine-shared-terminal-obligations-for-g).
It preserves their meanings, the direct acceptance of either premise, and the
option of supporting them through other propositions.

| Target | Exact existing content |
| --- | --- |
| `STMT-POTENCY-IS-CAPACITY-UNDER-PRIVATION` (`3c0b7bb3-1526-55a9-b71e-0d5fb3148782`), abbreviated **T** | `∀ x r, InPotency x r ↔ CanBe x r ∧ Deprived x r` |
| `STMT-PRIVATION-IS-LACK-OF-ACT-IN-CAPABLE` (`7c3da33e-7ead-54f8-aace-ed3cf3a7bb02`), abbreviated **Q** | `∀ x r, CanBe x r → (Deprived x r ↔ ¬ InAct x r)` |

The strongest positive finding is that **Q has a well-motivated conceptual
reading as absence of the relevant act in an apt subject; T then follows for the
already adopted unactualized-potency sense**. Aquinas's *De principiis naturae*
1–2 gives a more direct source lead for that subject/absence analysis than the
two support links presently attached to the targets. Aristotle's treatments of
change, capacity and privation provide complementary discrimination among the
relevant concepts. This is support for a selected meaning, not a stipulation
that all philosophical uses of potency or privation mean the same thing.

The new conditional analyses below are **unregistered analyst reconstructions**.
They have no new Lean, binding, Comparator or NanoDa certificate. Existing result
types and proof bodies were inspected; their recorded evidence is reused, not
reported as fresh verification. No statement, definition, source claim, formal
argument or graph status is changed by this note.

## Fixed meanings and existing support

Write `A`, `C`, `P` and `D` for the existing `InAct`, `CanBe`, `InPotency` and
`Deprived` predicates. These abbreviations introduce no new corpus vocabulary.
Every occurrence uses the same subject, respect, act predicate and evaluation
context. The target signatures have no explicit time parameter. Applying them
across times therefore requires a fixed-context reading or a faithful contextual
index; silently comparing act now with lack at another time is invalid.

The [potency definition](../../corpus/definitions/potency.json) already selects
POTENCY_1 as `C x r ∧ ¬ A x r`. It expressly distinguishes a capacity retained
during exercise and receptive potency of a principle to its received act.
The [capacity definition](../../corpus/definitions/capacity-to-be.json) leaves
`C` neutral about whether the act occurs. The
[privation definition](../../corpus/definitions/privation-in-capable-subject.json)
means a lack in a subject apt to have the form, illustrated by unshaped bronze;
it is expressly distinct from privation of a due good. The
[act definition](../../corpus/definitions/act.json) and
[respect definition](../../corpus/definitions/respect.json) remain framework
inputs. No causal efficacy, modal accessibility, capacity existence or empirical
application follows just from naming those inputs.

The original T declaration nevertheless accepts an independently supplied `P`.
Its adopted specialization and its generic theorem are different applications.
A POTENCY_1 label does not make every generic telescope definitionally adopted.
The [existing disambiguation](../../corpus/disambiguations/potency.json) already
requires this distinction.

### Exact reusable results

| Existing result | What can be reused | What it does not supply |
| --- | --- | --- |
| `b39f5282-fa9a-5433-a9ef-eebcac297295`, `POTENCY-IS-UNACTUALIZED-CAPACITY-FROM-PRIVATION` | `TruthCore.Results.Causality.Round3CogitoBase.potencyIsUnactualizedCapacityFromPrivation` composes T and Q into **F**: `∀ x r, P x r ↔ C x r ∧ ¬ A x r`. Its proof explicitly passes through `D`. | Warrant for either input, or a universal interpretation of an arbitrary `P`. |
| Existing helper `TruthCore.Latin.Aquinas.SummaTheologiae.AdoptedPotency.analysis` | F is definitionally true when `P` is exactly the adopted function. See [the module](../../TruthCore/Latin/Aquinas/SummaTheologiae/PrimaPars/AdoptedPotency.lean). | A corpus rule concluding generic F for a separately supplied potency relation. |
| `a26e8e49-ca29-55f0-81e6-411d72543c25`, `ACT-POTENCY-DEFINITIONAL-ANALYSES-CONSERVATIVE` | F entails same-respect act/potency non-overlap; conversely, generic non-overlap permits *some* capacity relation satisfying F. The witness may be `C := P`. | Fidelity of that existentially chosen capacity to the independently intended ability relation. |
| `e374c69d-d5e5-547c-a8a1-f8de313e6f76`, `ADOPTED-POTENCY-NONOVERLAP` | The adopted function and the explicit case-predicate noncontradiction premise yield non-overlap. | Non-overlap of capacity itself, or a defeat of receptive-potency accounts. |
| `b9c3f090-3bf2-5c96-ae3e-c18a1d63cd3b`, `ROUND3-COGITO-BASE-CONTROLS` | `capacityWithoutPotency`, `privationWithAct` and `potencyWitness` demonstrate omission behavior and joint satisfiability in the recorded small formal interpretations. | A real capable subject lacking potency, a real privation coexisting with its very act, or philosophical evidence against the intended meanings. |
| `2814c3db-a02a-5cd8-87b4-4751c884ef1a`, `CAPACITY-NON-SIMULTANEITY-FAILS-FROM-EXERCISE` | An actual exercised-capacity witness refutes the proposal that act and capacity never coincide. | An objection to adopted potency, which already distinguishes capacity from unactualized capacity. |

The existing route is T and Q → F, through argument
`804d2c83-cf37-5a1a-8534-13b8fcf5c307`. Both targets are common terminal inputs
under the published terminal-only expansion. This graph fact does not make two
independent metaphysical foundations obligatory. The direct-or-derived view
still permits prima facie acceptance of F; the adopted specialization can use
its existing definition. Additional support for T and Q remains useful even
where it shares that background.

## Sources inspected and their actual contribution

The following source readings support the reasoning; they are not new formal
attribution records. The Aristotle passages listed as materialized were acquired
and hash-checked with the existing `source_evidence.py materialize` command and
their Greek text was read with the identified English context. The other pages
were opened and read live; no byte-pinned corpus witness is claimed for them.

| Source and precise locator | Finding and scope |
| --- | --- |
| Aristotle, *Physics* I.7, 189b30–191a22; I.8, especially 191b13–17 and 191b27–29. [Hardie/Gaye translation](https://classics.mit.edu/Aristotle/physics.1.i.html). Existing passages `ARIST-PHYS-I-7`, `ARIST-PHYS-I-8` materialized. | The musical-man and bronze examples distinguish the persisting subject from the absent form; privation does not remain with the acquired form. I.8 distinguishes qualified lack from sheer non-being and identifies an act/potency account as another solution to the generation difficulty. These are useful structural support for T, but neither passage states the target's unrestricted biconditional over the supplied capacity predicate. |
| Aristotle, *Metaphysics* IX.1, 1046a29–35; IX.3, 1046b29–1047a20; IX.6, 1048a25–b9; IX.7, 1048b37–1049a18. [Ross translation](https://classics.mit.edu/Aristotle/metaphysics.9.ix.html). All four existing chapter witnesses materialized. | IX.1 distinguishes forms of privation. IX.3's builder argument gives reasons to distinguish ability from its present exercise: stopping and resuming does not normally involve losing and reacquiring the art. IX.6 contrasts actual exercise with available but unexercised ability and expressly proceeds by analogy. IX.7 requires a suitably prepared subject, rather than treating everything remotely transformable as already potentially the outcome. This favors a substantive, qualified capacity interpretation and the adopted sense; it does not supply one universal definition covering every potency usage. |
| Aristotle, *Physics* III.1, 201a10–b15. [Hardie/Gaye translation](https://classics.mit.edu/Aristotle/physics.3.iii.html). Existing passage `ARIST-PHYS-III-1` materialized. | Motion concerns the capable subject as capable, not the subject merely as bronze. The completed house and the buildable being built distinguish a terminal form from its ongoing actualization. This supports keeping the respect and stage fixed; the passage does not identify absence of the terminal form with absence of all actuality. |
| Aristotle, *Metaphysics* V.22, 1022b22–1023a7. [Ross translation](https://classics.mit.edu/Aristotle/metaphysics.5.v.html), chapter 22. Live reading only. | Privation has several senses, including lack relative to nature or genus, and lack at the time and in the circumstances appropriate to possession. The source supports specifying aptitude and context; it does not require replacing every broad subject-relative lack with the strictest time-qualified or evaluative sense. |
| Aristotle, *Categories* 10, 12a26–b5 and 13a3–18. [Edghill translation](https://classics.mit.edu/Aristotle/categories.3.3.html), chapter 10. Live reading only. | Sight/blindness concern an appropriate subject at the relevant natural stage. Possession of the visual faculty is not its exercise. The natural-stage qualification supplies a useful boundary on this narrower sense and prevents treating any absent attribute as a privation. It does not make an ordinary interval of not seeing an interval of blindness. |
| Aquinas, *De principiis naturae* 1–2: Corpus Thomisticum entries [69878]–[69879], especially chapter 1's generation analysis and chapter 2's subject, negation and acquisition paragraphs. [Latin](https://www.corpusthomisticum.org/opn.html); [Kocourek translation, §§7–13](https://isidore.co/misc/Res%20pro%20Deo/Aquinas/Bilingual/DePrincNaturae.htm). Live reading only. | Chapter 1 calls the missing actuality in generation privation: “non esse actu, quod est privatio.” Chapter 2 distinguishes negation from privation in an apt, determinate subject, and distinguishes the matter which persists from its lack of the acquired form. This directly supports the broad subject/absence analysis underlying Q and its connection to T. The account concerns generation and its eligible subjects; extending it to every respect in a generic signature remains an explicit interpretation step. The Latin and translation are two presentations of one source, not independent corroboration. |

The existing Physics snapshot is OpenGreekAndLatin/First1KGreek revision
`7881c563436f52fb3550e6daa6df94be1b83b0e3`, blob
`fcf9fac288fc2b7c37808fb8da037f310ac7211b`; the Metaphysics snapshot is
PerseusDL/canonical-greekLit revision
`a065c359aab33c33bd17ddc2cac7d27fdc9cd870`, blob
`4c03d2664d8acf43e49ce1b060d3e99f0e07c548`. Their URLs and selectors remain in
the existing passage manifests.

The two present support links are modest in scope:
`388eb17b-ee62-5010-82f6-82f94402dc1f` reads Physics I.8's qualified privation;
`4eb6f90c-55cd-59bd-8a25-48f9e09196a2` reads IX.6 as F. The latter already
records the generalization from examples and analogy. The newly inspected
Aquinas passage strengthens the case for a subject-relative privation analysis
without converting either existing support link into a stating attribution.

## Positive arguments and exact bridge obligations

### 1. From apt-subject absence to Q

For this reconstruction alone, let `Apt x r` mean that x is a suitable bearer of
the particular act/form r in the evaluation context. This is explanatory
notation, not a new registered definition or an unconstrained term being passed
off as a completed formalization. Distinguish suitability from actually
possessing r, and from a judgment that possession is morally required.

The sufficient bundle is:

1. **Subject-relative absence:** `∀ x r, D x r ↔ Apt x r ∧ ¬ A x r`.
2. **Capacity-to-aptness:** `∀ x r, C x r → Apt x r`.
3. The identical r, A and evaluation context on both sides of these formulas.

Given `C x r`, (1) takes `D x r` to `¬ A x r`. Conversely, (2) supplies the apt
subject, and (1) combines it with `¬ A x r` to give `D x r`. This yields Q by
two constructive directions; excluded middle is unnecessary.

The first premise articulates the existing broad privation meaning. Its warrant
is conceptual and source-supported: what makes this an intelligible *lack of r
in x* is both the missing r and x's eligibility for r. The second is credible
when `C` is an actual ability of this subject to receive/exercise r under its
specified conditions. A claim merely that something else could eventually
replace x, or that an outcome is logically describable, does not identify such
an ability. This is why a precise capacity relation adds information rather
than merely renaming absence.

This route does not require `Apt → C`. A subject may be apt by its kind but
currently unable to exercise the relevant faculty; Q is asserted only on C's
domain. Nor does it claim that an absent perfection is a separate positive
entity. Both T and Q remain compatible with treating D as a subject-relative
absence.

**Exact boundary:** this bundle supports the supplied broad privation predicate.
If a use instead selects privation of something naturally due *now*, premise
(1) needs that further condition. It then yields only the corresponding
qualified Q unless `C → DueNow` is separately supplied. That is an alternative
sense test, not a proposed restriction or silent revision of the present target.

### 2. From Q to T in the adopted sense

For the fixed adopted function `P x r := C x r ∧ ¬ A x r`, Q suffices for T:

- From P, retain C and use Q's reverse direction to turn the missing act into D.
- From C and D, use Q's forward direction to obtain the missing act, hence P.

Conversely, adopted T suffices for Q. Fix C. From D, T yields P and therefore
the missing act. From the missing act, the adopted definition yields P and T
yields D. Thus **under that exact adopted instantiation, T and Q are
constructively equivalent**. This equivalence is a new *unregistered analysis*,
not an added corpus theorem or a new edge in the terminal formula.

The result is useful support organization: the two recorded premises share one
subject/absence commitment under the adopted sense. They need not receive two
disjoint evidential histories. Their equivalence is not itself additional
warrant for Q; the conceptual account, source readings and correctly identified
examples supply that warrant.

### 3. The bridge for an independent potency predicate

For a generic supplied P, retain the existing statement **F**,
`STMT-POTENCY-IS-UNACTUALIZED-CAPACITY`
(`c85e8ef5-3dc4-502d-90f8-da1429e33fd8`).

F plus Q suffices for T by the preceding two directions, with F replacing the
definitional unfold. F plus T suffices for Q by fixing C and applying the two
biconditionals. The existing registered result provides T plus Q → F.
Accordingly, **conditional on F, T iff Q**; without F, the existing omission
controls show why Q alone says nothing about an unrelated P.

Using independently accepted F with Q is a legitimate alternative support
bundle. Deriving F from T and Q and immediately citing it back as independent
support for T adds no warrant. The direct IX.6 reading or the adopted definition
can provide a distinct entry point, while its semantic scope remains explicit.
The conservative-analysis result must not be used to identify an existentially
constructed `C := P` with the actual capacities under investigation.

### 4. Warrant from actual acquisition and retained competence

There is an ordinary, discriminating way to ground the concepts without asking
for an endlessly prior derivation. Distinguish a person's acquired skill from a
current performance, or material's readiness for a specified form from present
possession of that form. Evidence of successful exercise, interruption and
resumption without relearning gives a reason to take competence seriously while
distinguishing it from current activity. A suitable material that acquires a
form gives a corresponding case of eligible prior absence. Aristotle's builder
argument is an explicit source version of this reasoning; no new experiment is
claimed here.

The inference to a continuing capacity is defeasible. It assumes the same
subject and relevant competence, no intervening acquisition or destruction of
that competence, and the stated exercise conditions. It supports C's application
and the difference between C and A. It does not by observation alone establish
the universal biconditionals T or Q, or a remote metaphysical capacity for every
perfection. Combining this practical warrant with the conceptual analysis is
appropriate cumulative support; neither kind of reason has to stand alone.

A useful sanity check is a currently incomplete change. A body may already
have one temperature while being capable of a higher one. Set r to the precise
target state; do not identify being below that state with lacking every thermal
actuality. Likewise, the occurrence of building is an actuality of the process
while the completed-house condition is absent. These are analyst illustrations
of index discipline, not newly measured empirical results or a replacement
definition of motion.

## Serious alternatives and rejected shortcuts

**Capacity retained during exercise.** The positive rival reading takes P to
be a power possessed both while idle and while acting. It has a clear mechanism:
an instance `C ∧ A` would violate T plus Q if P were identified with C. Its
grounds include the skill/exercise distinction and the already registered
exercised-capacity result. This is relevant when someone transfers T to the
power sense. It is not an objection to the existing adopted sense, which keeps
that power as C and reserves P for its unactualized case. No blanket defeat of
powers or receptive-potency metaphysics is inferred.

**Natural-stage or due-possession privation.** This reading adds eligibility
conditions concerning age, organ, circumstances or due possession. Its concrete
reason is that a merely absent attribute need not count as the relevant defect;
the inspected *Categories* and *Metaphysics* passages exhibit the distinction.
The response is to preserve the actual form/faculty and scope. Not exercising
vision and lacking the visual faculty are different r values. The present Q
concerns broad apt-subject lack; the stricter reading needs an explicit bridge
before its conclusions replace Q. There is no source-backed reason here to
discard the broad sense or to impose moral due-ness on it.

**Merely conceivable counterassignments.** The existing controls assign
independent Boolean predicates so that one premise fails while others hold.
They establish a precise formal non-entailment. Their names do not independently
justify an actual case where privation of r and actual r coexist in the same
subject, sense and context. No such substantive objection to the selected Q
was identified in the inspected material.

**Rejected derivation shortcuts:** a source saying that generation has a
subject does not alone imply every capable, nonactual subject is in potency;
the named potency interpretation remains needed. Absence of a form alone does
not supply capacity. Possessing a capacity does not assert its current
actualization. Substituting a narrower privation sense without preserving its
conditions changes the premise. Cycling T/Q through F gives no independent
confirmation. None of these failures is evidence that the selected premises
are false.

## Proposed overall provisional judgment

For the **adopted unactualized-potency sense and the existing broad apt-subject
privation sense**, both premises are provisionally well supported as conceptual
articulations. The support combines prima facie intelligibility, the
subject/form distinction in ordinary acquisition, the skill/exercise
distinction, and the newly read direct Aquinas account. The important gain is
positive support for Q and a precise route from it to T, not an added count of
independent witnesses. Aristotle and Aquinas share a tradition and cannot be
counted as wholly independent empirical confirmations.

For a **generic independent P**, the same judgment does not automatically
transfer. It depends on F faithfully interpreting that P. For a supplied C,
application depends on its representing the subject's actual qualified ability.
These are exact semantic/application obligations, not defects consisting in the
absence of an independent proof for every primitive. The existing direct
assumption options remain reasonable to assess on their own merits.

The strongest standing alternative is the power-retained-in-exercise meaning;
it survives as a different interpretation and does not defeat the adopted one.
The narrower due-possession reading likewise survives in its scope. The formal
frontier is unchanged. This worker judgment is proposed for the coordinator's
independent semantic challenge before it is used as reviewed support.

## Strengthening, reopening and verification

Concrete next work is now separated from repeating the same source search:

1. **Registration:** when the coordinator's verification environment is usable,
   formalize the adopted T↔Q bridge and, if needed, the generic F→(T↔Q) bridge
   using existing declarations. Register exact premise bindings, compare with
   `b39f5282`, and run the required proof gates. No new general-purpose
   act/potency library is needed.
2. **Historical attribution:** if a structured source claim is wanted,
   materialize a legitimate *De principiis naturae* 1–2 witness under existing
   source rules, then register only the statement actually supported. The live
   reading above is persisted evidence; it is not an already pinned claim.
3. **Application:** inspect a consequential downstream instantiation's C, A, r
   and time/context. Confirm that every use is the same adopted predicate or
   has F explicitly available. A demonstrated mismatch would suspend the
   transfer to that consumer, not the whole selected conceptual analysis.
4. **Discriminating examples:** for a purported counterexample, record the
   exact absent act/form, aptitude, capacity and context. A genuine `C ∧ D ∧ A`
   or `C ∧ ¬A ∧ ¬D` under the *same broad sense* would challenge Q. A change to
   power, blindness, remote transformability or a different time is a sense
   change, not that counterexample. A concrete example can strengthen warranted
   application even though it does not prove the universal.

The selected question is substantively advanced: the sources, strongest
conditional bridges, actual rival meanings and direct warrant are documented.
Formal registration is blocked by the coordinator-reported missing verifier
toolchain, and changing shared definitions or downstream meanings is outside
this assignment. Neither barrier blocks the positive research judgment above.

Checks performed for this note and its two attempts:

- `truth related` and `truth dossier` for both targets; dossiers for F,
  exercised capacity and the Megarian thesis; `truth context` for the
  conservative-analysis result, followed by exact declaration/proof inspection.
- Materialized and read the seven existing Aristotle chapter witnesses listed
  above. No full-source refetch or source-status migration was performed.
- All 16 Boolean assignments to A, C, D and P satisfy the pointwise formulas
  `F → (T ↔ Q)` and `(T ∧ Q) → F`; this is a finite diagnostic alongside the
  written constructive reasoning, **not a Lean certificate**.
- `truth check` passed with the two new attempts loaded; the reported warnings
  concern existing closure and legacy sense records. Offline
  `corpus.py attribution-check --base 03d97b48a86d4b7d7bbedcb4441398ce3a9dadef`
  reported no new or changed stating claim. Diff hygiene is checked before
  handoff. No new Lean theorem, source-claim attribution or premise-closure
  change is claimed.
