# SCG I.22: a necessary *esse* and a contingent conjunction

Research slice for #1595 / #319, connected to the D → E question in the
necessary-being God route. This is an **analyst reconstruction** and a typed
test, **not a new historical source claim**: no chapter-specific SCG I.22
`corpus/passages/` record has been materialized and read in this branch.

Primary navigation: [Latin *SCG* I.22, oldid 132346](https://la.wikisource.org/w/index.php?title=Summa_contra_Gentiles/Liber_I/Caput_XXII&oldid=132346),
also [Corpus Thomisticum, lib. I cap. 22, nn.2–4](https://www.corpusthomisticum.org/scg1014.html)
and [CCEL English chapter XXII](https://www.ccel.org/ccel/aquinas/gentiles.iv.xx.html).
The public Latin and English were read as orientation witnesses, not certified
to the repository's source-evidence standard. CCEL's abridged English omits
the distinct nn.3–4 objection/reply; the Latin is essential here.

## Source content, with the boundary marked

- **n.2:** Aquinas starts from what he calls an *esse* necessary through
  itself. If such an esse were attached to a quiddity different from itself,
  the attachment would be repugnant or consonant. Repugnance excludes its
  being the quiddity of that esse; consonance introduces three explanatory
  directions: (i) esse depends on essence, (ii) both depend on another cause,
  or (iii) essence depends on esse. The first two conflict with his **per se**
  necessary esse, not just with its eternal/modal presence; the third makes
  the putative essence adventitious to the esse, not its own quiddity.
- **n.3, a real objection:** perhaps this esse does not absolutely depend
  on that essence for *whether it is*, but only for **the conjunction** by
  which the esse is attached to it. Thus the esse is necessary through itself
  while the conjunction is not necessary. This targets an illicit move from
  contingent union to the dependence of the esse itself. The difference is
  explanatory-relatum sensitive. n.3 also says where the dependence lies:
  *dependet quantum ad coniunctionem*, the esse depends on the essence for
  its conjunction. Its *non per se necesse* is therefore read in two sibling
  senses (see below).
- **n.4, the written reply, in two cases.**
  - *First case:* if that esse can be *understood without* the proposed
    essence, the essence is accidental **to that esse**; Aquinas then
    identifies the necessary being with *that esse*, so the proposed essence
    is accidental to the first necessary thing and not its quiddity. He allows
    it to be some essence posterior to God (*aliqua essentia Deo posterior*).
  - *Second case:* *Si autem non potest intelligi illud esse sine illa
    essentia, tunc illud esse absolute dependet ab eo a quo dependet
    coniunctio sua ad essentiam illam. Et sic redit idem quod prius.* If the
    esse cannot be understood without that essence, the esse depends
    absolutely on whatever its conjunction depends on, and the n.2 dependence
    horns return. This is a second written case, not the logical converse of
    the first conditional. (An earlier draft of this note wrongly said n.4
    has no such case; corrected after the owner's source-fidelity finding on
    PR #1602.) **It is not yet formalized; attribution deferred.** Its
    applicability needs explicit semantics for intelligibility, for the
    source on which the conjunction depends, and for *per se* necessary
    existence. It is not inferred from `NecessaryAt` or modal co-presence.

### Two senses of n.3's *non per se necesse*

- **Modal proxy (formalized):** the conjunction fails at some accessible
  world (`ContingentConjunctionAt`), and *per se necesse* of the esse is
  rendered by presence at every accessible world (`NecessaryEsseAt`).
- **Dependence sense (sibling reading, not yet formalized):** in SCG I the
  *per se*/*per aliud* distinction concerns whether something has a cause of
  its necessity, and n.3 frames the objection as dependence. On this reading
  a conjunction that is present at every world but depends on something
  satisfies n.3's description. *Per se necesse* (I.22) then belongs on the
  underived/uncaused side of `DISAMB-NECESSARY-EXISTENCE-VS-UNDERIVED`, not
  on the `NecessaryAt` side. This sense needs its own definition and Lean
  declaration together with the second-case relata (the source on which the
  conjunction depends, and absolute dependence of the esse); until then it is
  an open semantic obligation recorded in definition `b18c2550`.

Every claim below that something lies "outside" the reply is relative to the
modal proxy and to the first n.4 case.

The n.2 trilemma and the n.4 reply use a stronger self-necessary sense than
`NecessaryAt` alone: the actual *esse* is not derived from other principles
or causes, whereas `NecessaryAt` says only that a fixed bearer exists at all
accessible worlds. Likewise, `NoExistingSupportAt` excludes incoming edges
only from the selected support relation. Neither is a definition of *ipsum
esse subsistens*, and existing q.3 a.4 results already cover a different,
efficient-causal D → E route. We do not repeat that result.

## Exact new formal question

`TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22Conjunction`
imports the existing q.3 a.4 `Profile` for the bearer's actual represented
`esseOf` and `essenceOf`. It separately names the **proposed** quiddity q,
whose rejection need not deny the bearer's actual essence. It then keeps
these further relata **separate**:

| Relatum/relation | Lean field or definition | Meaning and limit |
| --- | --- | --- |
| Bearer `x`, actual essence and esse, proposed `q` | `q3`, `q3.esseOf`, `q3.essenceOf`, `proposedQuiddityOf` | A rejected q is not called the actual essence by stipulation. Success would need its own correspondence to `q3.essenceOf`; represented unequal principles do not by themselves settle real distinction. |
| Existence of esse itself | `esseExistsAt v e` | Not the same as a bearer's `ExistsAt v x`. |
| Necessary esse at `w` | `NecessaryEsseAt p w e` | The same `e` exists at `w` and all accessible worlds. No causal/grounding claim is encoded. |
| Conjunction with q | `joinedAt v e q`, `ContingentConjunctionAt` | The same pair can be joined at `w` but not at `v`; conjunction can change without `e` vanishing. |
| World-separation witness | `ModalSeparationAt` | Some accessible `v` has `e` but no `e–q` union. |
| Conceptual intelligibility apart | `conceivableApart e q` | Primitive, not identical with modal separation. The conversion is an OPEN analyst premise. |
| Accident relative to esse | `accidentalTo q e` | Ontic adventitiousness relative to that esse, not randomness or mere modal contingency. |
| First thing *is* that esse | `identifiedWithEsse x e` | Ontic identification primitive, explicitly not derived from two modal existence functions being coextensive. |
| Real quiddity | `isQuiddityOf x q` | Whether the proposed q is genuinely what x is; not presupposed just because `essenceOf x` names it. |

The non-transcription theorem
`necessary_esse_contingent_join_separates` derives `ModalSeparationAt`
from `NecessaryEsseAt ∧ ContingentConjunctionAt` using a **counterworld
witness with the same esse**. "Same esse" is a structural surrogate: the same
represented esse principle satisfies `esseExistsAt` at the counterworld.
Nothing links `esseExistsAt` to the bearer's `Ontic.ExistsAt`, to q.3
actuality, or to q's existence there, so the union may fail simply because q
is absent. That suffices for the first n.4 case, which concerns the esse
being understood without the essence. Dropping necessity breaks that inference: a
union may disappear only because its esse disappears. This solves a real
scope confusion and makes the argument able to fail.

The next theorem, `contingent_join_not_first_quiddity`, is explicitly
classified as an **assembly/transcription**, not independent philosophical
warrant. It uses three separate OPEN premises in order:

1. Modal separation warrants conceptual intelligibility apart. This is a
   substantive analyst interface and is not stated as a possible-world
   principle in n.4.
2. Intelligibility of e apart from q makes q ontologically accidental to e.
   This is the first n.4 case, attribution deferred.
3. If x is **identified with e**, a q accidental to e is not the genuine
   quiddity of x. This is the conclusion drawn within the first n.4 case,
   attribution deferred.

It concludes only that the **contingently joined q is not the quiddity of x**;
it does not conclude `q3.essenceOf x = q3.esseOf x`. It also does not require
`isQuiddityOf x q` and its negation at once; it tests the separately named
candidate without granting it. This matters because the objection would be
trivially excluded by conflating the *proposed* q with the bearer's actual
`essenceOf` before asking whether q is genuine.

## Finite controls and surviving rival

`controls` states seven exact Bool-world/Bool-principle/Unit-bearer
interpretations. The first has a necessary e at both worlds and an e–q union
only at the actual world; q is accidental, not genuine quiddity, while the
bearer's separately represented actual essence remains e. Four other
assignments with the same contingent union show that the reply cannot force
its conclusion when, respectively, (a) the modal→conceptual bridge,
(b) conceptual→accident bridge, (c) accident→nonquiddity criterion, or
(d) ontic identification of x with e is absent. A fifth omission lets e
disappear in the world where the conjunction disappears; it defeats the
structural separation premise while preserving the other two open bridges.

The **strongest remaining semantic rival** to an inference directly from
D to E is the seventh profile: e exists at both worlds; e and q are distinct
represented principles; they are permanently joined; q is a genuine
quiddity; neither separation nor accident is assigned. The encoded
**first-case** bundle of n.4 holds but has no antecedent to reject. This is
**not** a model of the whole n.3–4 reply: `conceivableApart` is false, which
is exactly the antecedent of n.4's second written case, and the profile has
no relation for the source on which the conjunction depends or for absolute
dependence of the esse. Adding the second case as an open premise
(`joined e q ∧ ¬conceivableApart e q → ∀ s, conjunctionDependsOn e q s →
absolutelyDependsOn e s`) and n.2's per se clause (`per se necessary e →
¬∃ s, absolutelyDependsOn e s`) would leave this profile standing only if its
conjunction depends on nothing. On n.3's own description (the esse depends
on the essence for its conjunction) it would then be refuted through n.2's
horn (i). A **co-fundamental union** whose conjunction depends on nothing lies
outside n.3's objection altogether. What it must answer is: n.4's second case
(by having no conjunction source), n.2's consonance trilemma (which needs a
coverage assumption), and n.6's union-causation principle (*quae per se non
sunt unum, si coniungantur, oportet per aliquam causam uniri*). None of these
is formalized here.

A separately certified `underived_distinct_boundary` control combines this
SAME profile with an empty `NoExistingSupportAt` graph on the single
necessarily present bearer; it verifies that the existing
`ActualUnderivedEssenceIdentity` is false. The bare non-entailment
{actual, `NecessaryAt`, `NoExistingSupportAt`} ⊬ `esseOf = essenceOf` is
**already witnessed** by the existing `TruthCore.Causality.UnderivedEssenceEsse.Controls`
(third conjunct, model `varying`; statement
`STMT-UNDERIVED-ESSENCE-INTERFACE-CONTROLS`). The new result adds only that
this existing boundary remains compatible with the n.4 first-case bundle.
The empty support relation does not mention the conjunction, so it does
**not** represent an uncaused union. It is not positive evidence that a real
self-necessary being can have genuinely distinct co-fundamental principles.
A philosophically stronger version might
argue that two formal aspects of one necessary reality need neither be
efficiently caused by the other nor by a third; that independent warrant and
its relation to Aquinas's richer **per se** necessity have not been established
here. An unargued 'anything is possible' objection would have no weight.

The direct n.3 objection itself also remains viable as a description of a
**posterior composite**: e can be independently necessary while q is its
contingently conjoined accidental adjunct, or q can be constitutive of the
composite object *e-with-q* whose existence is contingent. It does not thereby
make q the essence of the first being **identified with e**. Accepting the
ontic identification and n.4 accident criterion is the exact price of that
first-being move; treating merely existing-with-e as identification would beg
the question.

## Reuse, effect and next discriminating test

Reuses the existing q.3 a.4 `Profile` and does not add a parallel
`essenceOf`/`esseOf` implementation. The root target is D → E for the
necessary God-route; the currently certified conditional D → E remains
`ActualUnderivedEssenceEsse`, whose independent causal-support interfaces
are untouched. No formal result here establishes a new D → E route, an
intrinsic sufficient existence reason, or a claim about God. Intended and
actual root-route premise change: **none** (these are new outpost statements,
not new edges to the Catholicism root).

The recommended next slice (agreed by the owner's comment and the semantic
challenge on PR #1602) is **n.4's second written case**, as an explicitly
conditional Lean slice with OPEN semantics for intelligibility, for the
source on which the conjunction depends, and for *per se* (underived)
necessity, using the dependence sense of n.3 above. Its controls: (a) a
conjunction dependent on q, expected to be refuted through n.2's horn (i);
(b) a co-fundamental union with an empty conjunction source, expected to
survive the second case and pass to n.2's coverage and n.6. After that,
formalize **n.2's dependency trilemma in the same typed environment**, not
as one opaque `Distinct → Identity` bridge: separate (i) dependence of e on
q, (ii) a common source of e and q, and (iii) dependence of q on e, then test
coverage, the underivedness exclusion, and n.6's union causation against the
co-fundamental profile. The live question is whether a co-fundamental union
has a positive enough replacement account to challenge these premises, or
instead violates a substantively defended one. A selected original-text
source claim requires materializing and reading a chapter-specific SCG I.22
passage before attribution.

Validation: the corpus records are generated from
`specs/scg-i22-contingent-conjunction.toml`. Kernel, binding, Comparator and
NanoDa checks run in CI on PR #1602.

## Second n.4 case and the dependence sense (#1608)

Follow-up slice: `TruthCore.Latin.Aquinas.SummaContraGentiles.BookI.Chapter22SecondCase`,
results in `TruthCore.Results.Aquinas.SummaContraGentiles.Chapter22SecondCase`,
records from `specs/scg-i22-second-case.toml`, attempt
`d614232c-11fe-48ce-8a7e-500f1a532c8f`. Still an analyst reconstruction,
attribution deferred; the same orientation witness was re-read for nn.2–6.

**Senses.** Disambiguation `a4b9e53e-d4d9-4f15-bc7f-e5fa913a96ea`
(`PER_SE_NECESSARY`) records the modal proxy above as `PER_SE_NECESSARY_1`
(`NecessaryEsseAt`, with `ContingentConjunctionAt`) and the dependence sense as
`PER_SE_NECESSARY_2` (`PerSeNecessaryEsseAt`: the esse exists and nothing other
than itself is a cause of its necessity; with `DependentConjunctionAt`: the
joining depends on something). Every argument of this slice uses sense 2 only.
No bridge between the senses is asserted. One finite control shows they come
apart on n.3's own case: a permanent union that depends on q is dependent but
not modally contingent.

**New relata** (definition `d421e2c9-4eb2-4bef-bb63-6c502c7732b4`, all
world-independent OPEN primitives): `conjunctionDependsOn e q s`,
`absolutelyDependsOn e s`, `necessityFrom e s`, `essenceDependsOn q s`,
`perSeOne e q`.

**OPEN premises** (analyst statements, attribution deferred):

| Premise | Source orientation |
| --- | --- |
| `InseparableEsseInheritsConjunctionSource`: joined, not intelligible apart, joining depends on s ⇒ e depends absolutely on s | n.4 second case |
| `DependenceOnAnotherGivesNecessityFromIt`: absolute dependence on another s ⇒ s causes e's necessity | n.2 *si ab alio dependet, iam non est necesse esse* |
| `JoinedDistinctTrilemmaCoverage`: joined distinct q ⇒ e or its joining depends on some s ≠ e, or q depends on e | n.2 dilemma and trilemma, coarsened by the analyst |
| `ConsequentOfEsseIsAccidental`: q depends on e ⇒ q accidental to e | n.2 horn (iii) |
| `NonUnifiedUnionHasSource`: joined and not one per se ⇒ the joining has a source | n.6 union causation |

The n.2 clause is a premise, not part of the definition of per se necessity,
so its omission is a checked control. The coverage premise merges horns (i)
and (ii) into what they share (the esse, or its joining, depends on something
other than the esse). That makes coverage weaker than the text's trilemma in
its disjuncts, but **broader in domain**: n.2 states the trilemma only of *hoc
esse quod necesse est*, and n.4's second case speaks only of *illud esse*,
whereas both encoded premises quantify over every joined pair of distinct
principles. The results apply them only where e is per se necessary.

Two further scope notes (semantic challenge on #1618, F2–F3):

* The encoded n.2 clause is **stronger than the text**. n.2 says only that
  dependence on another is *contra rationem eius quod est per se necesse-esse
  … iam non est necesse esse*, which excludes per se necessity. The premise
  instead assigns `necessityFrom e s` to every esse that depends absolutely on
  another s, even one with no necessity at all. That is plausible for
  contingent dependents only if `necessityFrom` is read as "a cause on which
  e's being, and any necessity it has, depends". The results use it only for a
  per se necessary e, where the textual reading suffices.
* `PerSeNecessaryEsseAt` encodes only existence plus the *per se* (non *per
  aliud*) component. It has no necessity component proper: an existing esse
  that is necessary in no sense satisfies it whenever nothing causes its
  necessity. Hypotheses using it are weaker than full per se necessity, so no
  conclusion is overstated.

**Results** (all zero-axiom, Comparator and NanoDa locally green):

1. `essence_dependent_inseparable_union_excluded`, control (a) in general form:
   with the second case and the n.2 clause, an inseparable union of a per se
   necessary esse with a distinct q cannot depend on q.
2. `dependent_conjunction_not_quiddity`: both written n.4 cases in the
   dependence sense, by a constructive case split on intelligibility apart.
   It reuses the #1602 first-case premises but **not** the
   modal-to-intelligibility bridge. A proposed quiddity whose joining has a
   source other than the esse is not the esse-identified bearer's quiddity.
3. `joined_distinct_quiddity_rejected`: coverage plus horn (iii) plus (2): no
   proposed quiddity represented as distinct from the per se necessary esse
   and joined to it is the bearer's quiddity. This is the conditional n.2–4
   route. It rejects proposed quiddities only. Reaching `essenceOf = esseOf`
   further needs the proposal to range over the actual q.3 essence.
4. `non_unified_quiddity_union_self_sourced`: n.6 plus (2), without coverage:
   a genuine quiddity not one per se with the esse has a joining with *some*
   source not other than the esse (constructively `¬ s ≠ e`). The bound type
   does not say every source is the esse. That "only" follows from (2) under
   the same premises, not from this result.

**Controls on the #1602 stable distinct profile** (`second_case_controls`):

* (a) n.3's own description (the joining depends on q): every premise holds
  except the second case, so the second case is what refutes it, through n.2
  horn (i). A variant honours the second case but withholds the n.2 clause.
* (b) co-fundamental (unsourced, one per se): outside both senses of n.3. Both
  n.4 cases, the n.2 clause, the horn (iii) principle and n.6 hold, q is a
  genuine quiddity, and represented esse ≠ essence. **Only coverage fails.**
  With per se unity denied, n.6 fails instead.
* A self-sourced joining also satisfies everything except coverage.
* Further controls: an omission of the horn (iii) accident principle, and a
  positive separable q-dependent profile in which all premises, including
  coverage, hold and q is rejected.

**Answer to the #1608 question.** The stable distinct profile survives the full
encoded n.3–4 bundle (both cases, dependence sense) only with an unsourced or
self-sourced joining. With n.3's q-dependent joining it is refuted. The
surviving rival is the co-fundamental union. In this encoding its price is the
denial of n.2's (coarsened) coverage, together with per se unity of distinct
principles. The latter conflicts with n.6's **main premise**, *omne autem quod
convenit alicui quod non est de essentia eius, convenit ei per aliquam causam*.
The per se unum clause is only that premise's justification (*enim*), and the
conflict runs through the implicit step from *non est de essentia eius* to
*per se non sunt unum*. Neither the main premise nor that step is encoded.
Divine simplicity (*non autem pars eius esse potest, cum essentia divina sit
simplex*) yields only that esse is not a part of the essence but *aliquid
praeter essentiam eius*. A rival may accept simplicity in that sense and still
hold that the non-part esse is per se one with the essence. (Corrected after
the semantic challenge on #1618, F1. The first draft wrongly said n.6 rules
out per se unity "through divine simplicity".) Neither denial is refuted
here. The corpus also has no positive replacement account of such per se
unity, so it records no substantive objection to coverage either.

**Next tests:** (i) encode n.6's main premise (what belongs to a thing but is
not of its essence belongs to it through a cause) and its step from *non de
essentia* to *non per se unum*, and test both on the co-fundamental profile,
where simplicity supplies only *praeter essentiam*; (ii) n.6's self-causation clause against the
self-sourced profile; (iii) the bridge from rejecting every distinct proposed
quiddity to `essenceOf = esseOf`, connected to `ActualUnderivedEssenceEsse`;
(iv) the warrant for coverage as an independent premise.

## The full n.6: belonging, source location, and a co-constitutive rival (#1623, 2026-11-14)

### Newly pinned primary context and exact reuse

Passage `4eebc2d7-7aff-4d97-9734-6d192cdccf5c` is now a
**materialized, byte-verified Latin passage**
for all of I.22 [23710–23720] in `corpus/passages/aquinas-scg-i22-lat.json`.
It reuses the **identical page bytes** already pinned for SCG I.18 on
2026-11-05 (Corpus Thomisticum snapshot SHA256 `0959a251…`). The full range
was read, especially nn.2–4 and 6–9. This upgrades the source available for
**this** investigation; it does not retroactively certify the earlier
analyst statements as attributed claims. No new claim or Lean result is made.
The prior paragraphs' warnings about the unavailable chapter-specific witness
describe the state of the earlier PRs, not this new reading.

Two other already pinned witnesses were rematerialized and read:
`AQUINAS-DE-ENTE-C1-2` (cap.1 [69872], matter/form constitute the
essence of a natural composite, with form as its actuality and in its way
cause of the composite's esse), and `AQUINAS-ST-I-Q3-A7` (co., *tertio*,
the diverse-united-by-cause argument). The existing complete pinned
`ARIST-MET-VIII-6` was also rematerialized and read: its potential/actual
account explains proximate matter/form unity without a **further** uniter,
while allowing a mover in generation. Reuse the source analysis and existing
formal controls in `docs/notes/aristotelian-unity-h6.md` and
`docs/notes/composition-causal-scope.md`. The q.3 a.7 premise is already
represented by `DiverseUnitedOnlyThroughUnitingCauseReading`, and its
`CompositeUnitingCauseFromUnion` route retains five explicit premises.

### What n.6 actually needs

In [23715], the starting commitments are an already identified *first
uncaused cause*, the previously asserted simplicity of its **essence**, and
a supposition that its substantial esse is not identical with that essence.
Simplicity excludes esse as a **part** of that essence; with nonidentity,
it is something *praeter essentiam*. The next, **main** premise says that
what belongs to something yet is not *de essentia* of that thing does so
through a cause. Aquinas then *explains* this by the rule about the union
of things that are not one of themselves (*per se*). These are related
claims, not one automatically definitional identity:

| Relatum or transition | Exact interpretation burden |
| --- | --- |
| `e ≠ q` in the q.3 `Principle` representation | Does this denote two **real** constituents, or two descriptions/formal respects of one actuality? Inequality of values alone settles neither. |
| `¬PartOfEssence(e,q)` | Simplicity of the quiddity rules out esse as an internal part; this is not yet a claim that e is accidental, externally caused, or not one *per se* with q. |
| `OutsideQuiddity(e,q)` | The n.6 inference from nonidentity-plus-no-part to *not of the essence*. This needs a faithful criterion for *de essentia*; mere modal non-coexistence is not required. |
| `BelongsSubstantially(e,q,x)` | The esse of the **same** bearer x belongs to its actual quiddity q as substantial actuality, not merely that arbitrary represented principles are `joinedAt`. |
| `CauseOfBelonging(s,e,q,x)` | A cause of substantial esse belonging to q. This is not definitionally `conjunctionDependsOn e q s`, nor necessarily `absolutelyDependsOn e s` or a present efficient `CausesIn y x esse` edge. |
| `perSeOne e q` | Distinct principles may still be intrinsic co-principles of one subject; `e ≠ q → ¬perSeOne e q` is the **contested step**, not a consequence of distinct tags or simplicity of q alone. |

The [23715] causal horns classify s by **whether it is of q's essence**,
not by `s ≠ e` (the comparison in the existing n.2 coarsening and n.4
results). On the intrinsic-to-q horn, q would explain its **own substantial
being**, while q is only actual through the esse being explained; n.6's
priority-of-cause argument rejects that self-production. Aquinas expressly
allows an exceptional *accidental* self-causation through an already
substantially existing subject; it cannot be used to reject every form of
self-explanation. There is also a **kind-of-cause** restriction: the pinned
*De ente* cap.1 [69872] says form is, in its way, a cause of a composite's
esse **while belonging to its essence**; cap.3 [69874] expressly restricts
the impossible essence-to-own-esse production to the **efficient-cause**
sense. A formal or constitutive cause of substantial actuality therefore
does not by itself instantiate the prohibited efficient self-production.
This horn needs a bridge from `CauseOfBelonging` to sufficient **efficient**
existential production, or a separately defended contradiction in formal
explanatory priority. On the external-to-q horn, a quiddity that acquires its
substantial esse from an additional cause cannot be the quiddity of the
first uncaused cause. Neither conclusion follows solely from a source of
the **joining**; both require that the source causes the relevant substantial
esse belonging, and the external horn requires the relevant first-cause and
same-essence correspondence.

### Exact conditional skeleton and surviving model tests

The following is an **unverified analyst inference plan**, not an added Lean
theorem or an attribution of its extra bridges to Aquinas. Fix one **actual**
first bearer x, its represented esse `e = q3.esseOf x` and **actual** essence
`q = q3.essenceOf x`. Assume `IsQuiddityOf x q`, substantial `joinedAt` and
actual presence, nonidentity, a simple quiddity, and firstness in a named
causal relation. To reach a contradiction from `e ≠ q`:

1. Supply `OutsideQuiddity(e,q)` from the source's no-part step, and
   `BelongsSubstantially(e,q,x)` from a real substantial constitution—not
   from mere arbitrary `joinedAt`.
2. Apply n.6's **OPEN** main premise to obtain some
   `CauseOfBelonging(s,e,q,x)`. One possible route derives it from the
   already encoded `NonUnifiedUnionHasSource` **only with** the additional
   `OutsideQuiddity ∧ BelongsSubstantially → ¬perSeOne` and
   source-relatum correspondence. The main premise may instead be taken as
   a separately open direct causal principle; that is not its warrant.
3. Divide causes by `OfQuiddity(s,q)`. If yes, require the substantive
   bridge from causing q's substantial esse to **efficient** self-production
   or prohibited formal-priority circularity of **q**, preserving n.6's
   formal/efficient distinction and accidental/substantial exception.
   If no, require the bridge from the external cause of q's substantial
   esse to the loss of x's firstness **when q is genuinely x's essence**.
   Neither bridge is supplied by `s ≠ e` or by arbitrary R-underivedness.
4. Only after both horns, with the q bound to this same x and the source
   relation mapped to the imported q.3/actual-R interpretation, infer
   `q3.essenceOf x = q3.esseOf x`. The current
   `ActualUnderivedEssenceEsse.ActualUnderivedEssenceIdentity` remains
   conditional on its **different**, already registered efficient-causal
   interface; no new root edge or discharged premise results here.

The previously checked `coFundamentalProfile` has `e ≠ q`, a genuine q,
permanent joining, `perSeOne e q`, and **no** conjunction source. It satisfies
the old encoded n.6 union clause, both n.4 cases and all relevant old
premises **except** n.2 coverage. An extension setting
`OutsideQuiddity = true`, `BelongsSubstantially = true` and
`CauseOfBelonging = ∅` would **fail** the newly stated n.6 main premise.
Setting `OutsideQuiddity = false` or denying substantial belonging instead
evades that premise but rejects, respectively, step 1's *de essentia*
reading or its same-bearer substantial application. These extensions are
transparent **proposed truth assignments**, not checked new finite models or
evidence of metaphysical possibility. The certified old control remains
unchanged; it is **not** a countermodel to the full historical n.6.

The existing `selfSourcedProfile` assigns the source of `e–q` joining **to
e itself**. That is not automatically the *intrinsic-to-q* horn and does
not instantiate n.6's self-causation conclusion: n.6 first divides
sources relative to **q**. Under `OutsideQuiddity(e,q)`, s=e lies on the
**external-to-q** side, even though s=x may be the first esse-identified
bearer. **For the new typed predicates this classification requires an OPEN
semantic bridge**: `OutsideQuiddity(e,q) → ¬OfQuiddity(e,q)`, with both
relations using the same sense of *de essentia*. The old model has neither
predicate, so its horn position is **not** already certified. The strongest
next test is therefore whether s=e actually gives
q substantial esse and, if q is x's genuine constitutive essence, whether
the resulting x→q priority conflicts with q's constitutive priority for x.
One may not infer an incoming `y ≠ x` efficient cause of x merely from
`s=e ≠ q`; that would equivocate between the source's relation to q and
its relation to x.

### Positive rival, warrant and next discriminator

The strongest **grounded** rival mechanism is **immanent constitution**:
Aristotle H.6 explains a natural composite's unity through proximate
potential matter and actual form rather than through two independently
actual things requiring a third tie; Aquinas's *De ente* cap.1 gives matter
and form distinct constitutive roles **within the composite essence**.
This independently motivates a denial that `distinct principles → not one
per se` holds unrestrictedly. It does **not** yet defend a co-fundamental,
unsourced union of **esse outside the quiddity** of a necessary first:
in the actual example both matter/form are de essentia of the composite,
form actualizes matter asymmetrically, and a productive cause is allowed.
Transferring it to e/q must give a positive account of their identity as
one substantial act, the necessity and sufficiency of their co-obtaining,
and why the nature of q does not make e a separately received perfection.

A second positive form of the remaining challenge is a **whole-first**
account: an intrinsically actual first whole has real internal structure,
while that structure is explained by the whole instead of a prior external
source. This is the already investigated priority-monist/reverse-priority
mechanism in `docs/notes/composition-causal-scope.md`, not a newly
verified metaphysical witness. Its cost here is to defend how derivative
internal structure can nonetheless be the actual **constitutive essence**
of the first without explanatory circularity. A merely formal-aspect
account avoids real plurality, but then `e ≠ q` in the current profile is
not by itself a faithful encoding of a **real** essence/esse distinction.

**Provisional assessment, this passage and baseline `4fffde08` (2026-11-14):**
the full n.6 gives a more serious conditional objection to the co-fundamental
model than the formerly encoded union rule: its main causal premise directly
challenges unsourced substantial esse belonging, and it distinguishes two
source locations plus a specific self-production argument. It is therefore
reasonable to favor this **conditional explanatory challenge over the bare
co-fundamental tag**. But the general causal principle, its *non de essentia*
and *non per se unum* bridges, and its application to the **same actual
first R-underived bearer** are not independently warranted by these texts
or established by a theorem. A serious immanent-constitution argument
survives against the universal diversity-to-uniter step; its transfer to
a first essence/esse pair is unresolved, not a refutation. No premise
establishment or root closure changes. Revision would require either a
defended actual first-esse application of the causal principle, or a
non-circular first-esse co-constitution that survives both causal horns.

Next discriminating formal test when the pinned Lean toolchain is available:
extend the **existing** `DependenceProfile`, retaining the q.3 actual essence,
with independent `BelongsSubstantially`, `OutsideQuiddity`,
`CauseOfBelonging` and `OfQuiddity` predicates. First contrast the direct
main premise with the derivation from per-se nonunity on the same old
co-fundamental control; then test the `s=e` external-to-q case and each
intrinsic/extrinsic horn separately, preserving all necessary actual-presence,
firstness, causal-kind, substantial-vs-accidental and same-bearer assumptions.
In particular, the existing joining-source `s` is a **Principle**, whereas
q.3 efficient `CausesIn y x esse` has a **Being** source; source presence,
realization of an internal principle by a bearer, numerical distinctness and
the actual-R bridge all need explicit, typed correspondence. Reject a
purported bridge if it merely identifies `conjunctionDependsOn` with
causing substantial esse. Independently compare I.22 n.8 [23717]: it treats
real distinct co-requisites as a composite and assumes the **previously
defended** absence of composition. This is an alternative conditional
support route; it is not a proof of the contested n.6 bridge and it must
not take essence=esse as an input to the simplicity proof. Also compare
I.22 n.7 [23716], which treats distinct essence/esse as potency/act and
invokes the previously asserted absence of potency in the first. The
potential/actual immanent-unity mechanism therefore incurs a **second**
independent conditional objection at a pure-act root, even if it escapes a
third uniter. The actual scope and warrant for `e ≠ q → potency in the
same first x` must be defended, not inferred from two Principle labels.
