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
