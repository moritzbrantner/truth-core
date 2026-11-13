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
