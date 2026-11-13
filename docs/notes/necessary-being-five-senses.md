# Five readings of necessary existence, nature, explanation, and underivedness

Status: **analyst map / open bridges**, not a new historical attribution or a
proof of the existence of God. Research issue: #1595. Related earlier work:
#312, #319, #1590, #1593.

The central discipline is to keep the *explanandum*, its putative *source*, and
the *kind of relation* typed separately. A fact about an aspect of a square
can be explained by its nature or side length without saying that the square
itself is existentially posterior to its own side length. Likewise, the fact
that a necessary bearer exists and the claim that its own nature explains
its existence are not interchangeable without a bridge.

| Label | Selected sense / precise question | Current formal home | Status |
| --- | --- | --- | --- |
| A: modal necessity | Does **this being** exist at every world accessible from the selected world? | `NecessaryAt m w x` in `German/Kant/CosmologicalInference` | Defined; modal scope is frame-relative. |
| B: own essential existence | Is **this being's existence fact** included in **its own nature**? | `OwnEssentialExistence p x` in `Explanation/EssenceReasonSeparation` | Analyst primitive `InEssence x (.fact x)`; essence semantics deliberately open. |
| C: sufficient intrinsic explanation | Does this being's nature adequately explain **why its existence fact obtains**? | Existing `ExistencePSR.Reason.intrinsic` and `CandidateIntrinsicReason p w x`; modal-sufficiency analogue `BruteFoundationExplanations.NecessitatesExistenceAt` | A *candidate token* and `explains` assignment do not prove adequacy; necessitation is a separately defined stronger condition, not by itself complete metaphysical explanation. |
| D: existential underivedness | Is **this being's existence** unsupported by distinct prior bearers (under a specified support relation)? | `NoExistingSupportAt`, `ActualUnderivedEssenceIdentity` in `Causality/ActualUnderivedEssenceEsse` | Typed, but dependent on the chosen support relation and selected-world / all-world quantifiers. |
| E: essence–esse identity | Is a bearer's *essence of* and *act of existence of* represented by the same actuality? | `p.esseOf n = p.essenceOf n` in `Causality/ActualUnderivedEssenceEsse` | Defined in an explicit Thomistic profile; not synonymous by definition with A–D. |

## What follows, and what does not

1. **A does not, by itself, yield B or C.** Modal existence says where the
   bearer exists, not why, or whether existence belongs to its nature. The
   first two finite controls in
   `Results/Explanation/EssenceReasonSeparation/Solution` exhibit
   `A ∧ B ∧ ¬CandidateC` and `A ∧ CandidateC ∧ ¬B` with true existence facts.
   They refute automatic *logical* identifications of these primitive formal
   relations; they are **not** evidence that the metaphysical readings are
   jointly possible, nor that candidate C is genuinely sufficient C.
2. **B and C are not lexical synonyms on the current meanings.** A claim that
   existence belongs to a being's essence is not yet an account of how that
   essence explains the actuality of its bearer. The precise bridge under
   investigation is `OwnEssentialExistence → AdequateIntrinsicExplanation`,
   where the consequent needs an adequacy criterion distinct from a token.
   Reuse `BruteFoundationExplanations.NecessitatesExistenceAt` as the **modal
   sufficiency test** rather than inventing another. Its existing theorem
   `necessaryReasonAndNecessitation` already proves that a reason necessary
   across the frame *and* sufficient in this sense entails A; neither
   premise follows from essence membership alone.
3. **B and modal dependence have different subjects of attribution.**
   `EssenceRequiresExistence p x y` means the nature of **x** requires the
   existence of **y**. `ModalRequiresExistence p w x y` means that in every
   accessible world, if x exists then y exists. If y necessarily exists,
   the modal claim is automatic for every x. In a finite model, both x and y
   necessarily exist and mutually modally require one another, while only
   x's essence is stipulated to require y's existence. Thus modal
   co-presence cannot recover source-indexed priority.
4. **C and D are not converses without further premises.** A noncausal
   intrinsic reason for an existence fact does not by itself exclude other
   supporters; and merely excluding external supporters does not manufacture
   a reason in the bearer's nature. Independence must name the relevant
   dependence: efficient-causal, existential-grounding, explanatory-fact,
   or essence-indexed. The four senses may overlap but are not identical.
5. **D-to-E already has a conditional route.** The existing
   `Results/Causality/ActualUnderivedEssenceEsse/Solution` applies Aquinas's
   essence–esse argument to an actually present, underived necessary bearer
   under explicit actuality, exhaustive-cause, and no-self-cause premises.
   Reuse this route; do not silently rewrite its substantive bridges as
   definitions. **E-to-C** is a further question, not yet proved by equality
   of profile fields alone.

## Ordering, aliasing, and the next formal bridge

`x depends on y` is not automatically a partial order. If an asymmetrical,
transitive **strict** metaphysical-priority relation is justified, its
reflexive closure yields a **non-strict** partial order; the direction is
`y prior to x` when x depends on y. Causal cycles, symmetric mutual
necessitation, and multiple grounding notions prevent this from being a
generic property of all things casually called “dependence”. The precise
relation and its laws must be supplied, not inferred from the word.

Aliases are permissible **only within a selected sense** with a proved or
definitional equivalence. E.g. “underived” and “no incoming support” can be
aliases if both mean the *same* support relation, world, and quantifier scope.
“Independent” meaning “can exist without y” is not an alias of “not
existentially grounded by y” when y necessarily exists: there is no world
without y, whatever x's grounding relations are. An unrelated necessary
thing is a counterexample to this unrestricted modal test, not a refutation
of existential underivedness.

## The Thomistic candidate: identity before explanatory adequacy

In Thomistic usage, **esse** is the act of being, not simply the proposition
`ExistsAt w x`. To call a source *subsistent esse itself*, or to say that its
essence **is** its esse, gives a strong intrinsic characterization. The
further slogan “its nature is the sufficient reason for its existence” can
be treated as an **interpretative gloss** on that characterization only in a
selected, non-efficient sense of reason. It is not a further efficient cause
from a pre-existing essence to its own bearer, and it is not automatically
the strictly prior ground of the very same existence fact. Otherwise a
strict, irreflexive metaphysical-priority relation would require a self-loop.

Aquinas **argues** for the identity instead of assuming every modally
necessary thing satisfies it. The following source passages give several
positive routes, each with an identifiable further burden:

| Route | Source's positive reasoning | Live bridge to check in Truth Core |
| --- | --- | --- |
| External-cause dilemma | If essence and esse differ, esse is received from an external efficient source or from the essence's principles; the latter cannot efficiently originate the bearer itself. A genuinely first efficient source cannot have external receipt. | *ST* I q.3 a.4, first argument; existing `Question3.Article4` and `ActualUnderivedEssenceEsse` already formalize the conditional underived-to-identity inference. Do not duplicate it. |
| Actuality versus potency | Esse makes an essence actual. If they are really distinct, the essence relates to esse as potency to act. Pure actuality excludes that potency; hence no such distinction in the first actual being. | *ST* I q.3 a.4, second argument; requires a defended **real** distinction/potency bridge, not merely differing concepts of essence and existence. |
| Participation versus firstness | A being that has existence without being its existence has being by participation. A source prior to participated being cannot be another participant on the same terms. | *ST* I q.3 a.4, third argument; defend participation/received-being and actual firstness, not just modal necessity. |
| Dependency trilemma | Given a genuinely **self-necessary** act of existence distinct from essence, either esse depends on essence, both derive from another, or essence depends on esse. The first two compromise underived self-necessity; the third makes the supposed essence adventitious rather than constitutive. | *SCG* I.22, first argument; preserve each horn and its notion of dependence. “Necessary through itself” here is **stronger** than `NecessaryAt` alone. |
| Noncomposite first being | A distinct essence and esse would be co-constituents of a composite actuality. The first, utterly simple being cannot depend on such a composition. | *SCG* I.22, concluding argument; reuse existing composition/firstness results and inspect whether they assume the disputed essence/esse decomposition. |

The especially useful new investigation is the *SCG* I.22 trilemma. It does
not claim that necessary **co-existence** implies dependency; the claim is
about which principle accounts for the concrete bearer and whether that
principle could be constitutive if it were ontologically **posterior**.
It therefore directly tests the owner's asymmetry/priority distinction.

**Direct objection and answer in the Latin chapter.** The abridged public
English presentation does not include the full intermediate reply, but the
Latin *SCG* I.22 nn.3–4 does. Aquinas considers the possibility that the
**esse itself** is unconditionally necessary, whereas its *conjunction*
with this particular essence is contingent. He replies in two cases:

- If this esse can be understood apart from that essence, the essence is
  accidental/adventitious **to the self-necessary esse**, so it is not the
  quiddity of the first being. A distinct essence could belong to some
  posterior bearer, but not constitutively to the first source.
- If this esse cannot be understood apart from that essence, its being is
  dependent upon whatever explains the conjunction, reviving the original
  burden. Here “cannot be understood apart” must **not** be replaced with
  mere `∀v, ExistsAt v esse → ExistsAt v essence`: if both are necessary,
  that extensional condition is trivially satisfied. The relevant premise
  is constitutive/non-accidental necessity *of the union*, and its source.

This gives a source-backed **argument against a specific proposed
essence/esse separation**, not a license to turn all modal co-existence into
ontological identity. Its important distinction is between the *necessary
esse* and the *conjunction of that esse with a proposed quidditative source*.
For a Lean test, explicitly type the two relata and conjunction, split the
two intelligibility/constitution cases, and add controls for (a) accidental
attachment that never becomes the first being's essence and (b) necessary
co-presence with no stipulated constitutive union. Do not bake the conclusion
into the definition of “through itself.”

**Related intrinsic-reason readings, not aliases across authors.** Leibniz's
*Monadology* §§44–45 connects a necessary being whose essence involves
existence with a being having the reason for its existence in itself;
possibility-to-actuality is part of this Leibnizian proposal. Spinoza's
*Ethics* I, definition 1 **does** define `causa sui` through essence
involving existence, with substance's existence then argued in proposition
7. These supply legitimate, *selected-sense* bridges from B to a non-efficient
intrinsic-reason sense of C. They do not show that merely recording the
equality `essenceOf x = esseOf x` explains *why that actual being exists*,
or that A (modal necessity) independently suffices. A Thomistic self-
subsistent esse and a Spinozist *causa sui* are not identical notions just
because both reject a distinct external efficient origin.

Two separate implications must remain visible:

1. **Underived first actual being + Thomistic dependence/composition
   premises → E (essence–esse identity)**: multiple Thomistic arguments
   support this, conditional on their specified dependence senses.
2. **E + selected account of intrinsic, noncausal intelligibility → C
   (adequate reason in itself)**: this is approximately definitional *if C
   is explicitly defined as self-subsistent actuality with no distinct
   existential ingredient needing reception*. If C instead demands a
   nontrivial sufficient grounding explanation of the existence fact, E
   alone does not provide one. Do not alias these two C-senses.

Next proof work should reuse the first route and test *SCG* I.22's three
dependency horns as a separate premise package, with a nonvacuous actual
necessary bearer, an explicit interpretation of what counts as “through
itself,” and an omission control for each substantive horn. No new source
claim is attributed yet: this mapping uses a public English translation **and
the Latin text of I.22 nn.2–9**, but the repository's pinned chapter-specific
source evidence should be
checked or extended before creating formal source-claim bindings.

Primary passages read: [*Summa Theologiae* I q.3 a.4](https://www.newadvent.org/summa/1003.htm)
and [*Summa contra Gentiles* I.22](https://www.ccel.org/ccel/aquinas/gentiles.iv.xx.html)
(compare [Latin I.22, nn.2–9](https://la.wikisource.org/w/index.php?title=Summa_contra_Gentiles/Liber_I/Caput_XXII&oldid=132346));
also [Leibniz, *Monadology* §§44–45](https://en.wikisource.org/wiki/Monadology_(Leibniz,_tr._Latta))
and [Spinoza, *Ethics* I def.1, prop.7](https://en.wikisource.org/wiki/Ethics_(Spinoza)/Part_1).

**Next work, tied to the God-existence route:** reconstruct the corpus bridge
`STMT-NECESSARY-GROUND-HAS-INTRINSIC-REASON` (issue #319), and the
independence/priority usage identified in #1595. Formulate a typed
source-indexed connection from a being's **nature** to its reason token,
**reusing** `BruteFoundationExplanations.NecessitatesExistenceAt` for the
necessitating component; do not assume that modal sufficiency alone exhausts
adequacy. Investigate the conditions under which **B** plus modal-essence
realization yields **A**, or **E** plus an essential-reason principle yields
**C**. Preserve
each bridge as an open premise until its semantic and argumentative warrant
is established; rerun the support formula after changing any route.

## Sources and limits

- Kit Fine, “Essence and Modality” (1994): essence is not defined by mere
  necessary truth; nature-indexed identity and dependence remain distinct.
- Leibniz, *Monadology* §§44–45: reason for the necessary being's existence
  found in itself; this motivates but does not prove the B/C bridge.
- Spinoza, *Ethics* I, definition 1: the essence of the *causa sui* involves
  existence; do not silently translate this into efficient self-causation.
- Aquinas, *Summa Theologiae* I q.3 a.4: the conditional essence–esse
  identification through an efficient-causal dilemma is already formalized
  elsewhere in the repository. Attribution of the five-column map to these
  authors is **not** claimed.
