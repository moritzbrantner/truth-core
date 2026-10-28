# External dependence on the eternity path

The current root route uses `STMT-IMMUTABLE-IS-ETERNAL` through the existing
`GodIsEternal` result. That bridge remains an explicit open premise. This reading
preserves the meanings of `PureAct`, `IsImmutable` and primitive `Eternal`.
It neither adds a duration ontology nor changes the default root route.

## Verified source context

The full Latin articles were materialized and read, including objections and
replies. The durable passage records are `AQUINAS-ST-I-Q9-A2` and
`AQUINAS-ST-I-Q10-A3`, `AQUINAS-ST-I-Q10-A4`, `AQUINAS-ST-I-Q10-A5`; q.9 a.1,
q.10 aa.1–2, and q.3 aa.1 and 4 supply context. They reuse the existing SCTA
Leonine diplomatic TEI snapshots, revision
`f9065dc8ce7bc790b8c972e49ee19d661f028be6`, with unchanged Git blob hashes and
license. The records, rather than temporary research exports, locate the text.
Diplomatic transcription noise does not erase the relevant complete clauses.

- Q.9 a.2 distinguishes potency **in the subject** from potency **in another**.
  The creator continually gives creatures esse; withdrawal would reduce them to
  nothing. An incorporeal creature can lack intrinsic potency to nonbeing yet
  remain subject to this external power. See
  `AQUINAS-ST-I-Q9-A2-EXTERNAL-MUTABILITY`.
- Q.10 a.3 distinguishes proper eternity from participated or extended uses:
  never ceasing, long duration, or stable being and operation. These are not
  automatically proper eternity. See
  `AQUINAS-ST-I-Q10-A3-PROPER-PARTICIPATED-ETERNITY`.
- Q.10 a.4 maintains the distinction even if time had no beginning or end:
  temporal succession remains different from proper eternity. That conditional
  comparison does not endorse an eternal world. See
  `AQUINAS-ST-I-Q10-A4-ENDLESS-TIME-SUCCESSIVE`.
- Q.10 a.5 permits aevum to be internally all at once while admitting adjunct
  actual or potential change. Its future existence can remain subject to divine
  withdrawal. Proper eternity excludes that compatibility with before and
  after. See `AQUINAS-ST-I-Q10-A5-AEVUM-ADJUNCT-CHANGE`.

## Conservation reading and its limits

The additional evidence is the pinned Latin `AQUINAS-ST-I-Q44-A1` and the
translated `AQUINAS-ST-I-Q104-A1-EN`. The latter uses the existing New Advent
English Dominican translation mechanism: the admitted SCTA transcription does
not cover q.104. Its response bytes and selected article text matched on two
fetches. Translation-based claims say `basis: translation`; they are not treated
as readings of the Latin q.44 witness.

Q.104 a.1 distinguishes indirect preservation by preventing corruption from
**direct, per-se conservation of esse**. A guardian can preserve a child from
fire without thereby being a direct giver of the child's esse. A builder can
cause a house to come-to-be without remaining the direct cause on which its
continued being depends. The article's divine application describes
conservation as the continuation of the action giving esse, not a new temporal
production at every instant; reply 4 expressly says the action is without
motion or time. These are the bounded readings
`STMT-DIVINE-ESSE-CONSERVATION-CONTINUES-GIVING-ESSE` and
`STMT-BECOMING-CAUSE-NEED-NOT-SUSTAIN-BEING`.

Q.44 a.1, including reply 1, connects participated esse to being caused by
another (`STMT-PARTICIPATED-ESSE-REQUIRES-OTHER-CAUSE`). Its reply 2 also warns
that an effect's necessity does not by itself exclude an efficient cause.
Neither that text nor q.3 a.4 licenses the inverse inference from
**essence–esse identity** to absence of an external cause.

For obligation B the narrow proposed reading is:

> If c directly conserves x's esse as its continuing giver, then c is a cause
> of x's being in the relevant esse sense; to use the maximum exclusion, c must
> also be distinct from x.

`DirectConservesEsse(c,x)` here is a name for a proposed interpretation, not an
introduced Lean predicate or a definition that includes `CausesIn c x esse`.
The exact interpretation into the existing `CausesIn` relation remains open.
Q.104 supports this scope through its giving-esse account; it does not justify
quantifying over every guardian, builder, arbitrary nonexistence counterfactual,
or power described only modally. The universal source reading and its
application to the same maximal root witness would both have to be explicit
before advertising a further derived result.

If that interpretation is defended, the already checked
`maximumHasNoDistinctEsseCause` theorem could rule out a distinct direct
conserver of that same maximum. Its companion `quartaViaWitness` imports the
existing Fourth Way theorem to supply the witness. This identifies a concrete
connection to consume; it does not perform a new inference merely by drawing a
support edge. In particular, it would still not exclude every arbitrary action
or withdrawal power of another being, and it would not supply obligations A or C
below. This source-only change adds no result, changes no primitive predicate,
and closes no frontier node.

## A structural consequence already available

`MAXIMAL-BEING-EXCLUDES-DISTINCT-ESSE-CAUSE` proves that a maximum in being has no
**distinct cause of its being in the existing `CausesIn` relation**. Its only
philosophical input is the already sourced
`STMT-CAUSE-OF-QUALITY-IN-ANOTHER-IS-MORE-SUCH`: a distinct cause at `esse` would be
more in being, contradicting `IsMaximumIn`.

`QUARTA-VIA-WITNESS-WITHOUT-DISTINCT-ESSE-CAUSE` imports the existing
`QuartaVia.quartaVia` theorem and applies that consequence to the same witness
which is maximal and causes the being of all other beings. It consumes the four
existing Fourth Way premises plus the existing causal-comparison premise. It
adds no maximum-existence, identification, or independence premise. It is not
another root wrapper, and it does not close the eternity frontier node.

The finite omission model has two maximal beings, no strict comparisons, and a
distinct causal pair. It shows why maximality without causal comparison does not
supply the exclusion. This is an encoded non-entailment example, not an alleged
theological possible world.

Q.3 a.4's first proof gives a different direction:
`STMT-DISTINCT-ESSE-REQUIRES-EXTERNAL-CAUSE`. If a thing's esse differs from its
essence, its esse must be caused by another, since its essential principles
cannot suffice to cause its own caused esse. The application invokes God as
first efficient cause. **Essence–esse identity alone does not yield absence of
an external cause by the inverse of this conditional.**

The existing `GodIsInfinite.godIsInfinite` proof derives esse–essence identity
locally from the imported simplicity result. `FirstMoverIsFirstBeing` derives
absence of distinct `PriorSimply` predecessors through maximality and the
separate priority-to-cause premise. Neither result identifies sustaining
dependence or withdrawal power with `CausesIn`. The new argument uses maximality
directly instead of inventing that identification or reversing q.3 a.4.

## Three remaining obligations

A. Relate genuine intrinsic and adjunct change capacity to the existing
`InPotency` relation. The present `PureAct` quantifies potency in the subject;
q.9 a.2's power in another is a distinct channel, not an implicit extra respect.

B. Relate the relevant **ongoing sustaining dependence** to a **distinct cause
of esse**. Q.9 a.2 motivates the reading for creatures whose esse is continually
given, but the relation and scope have not been encoded or defended. A claim
about efficient causing of esse, actual continual conservation, a power to
withdraw that conservation, and arbitrary modal power are four different
claims. The new exclusion theorem establishes only the first. It does not
exclude all possible actions of another merely because they are called powers.
The full root context supplies a maximal witness; this argument is not a
universal claim about every arbitrary `PureAct` object.

C. Recognize the intended proper eternity from a sufficiently full account of
life, succession and independence. Primitive `Eternal` is not silently defined
as temporal omnipresence, within-life constancy, or an enum label. A recognition
premise cannot be advertised as a derived conclusion while it remains open.

## Omission cases to retain

These are descriptions of necessary modeling controls, not newly verified Lean
results or refutations of Aquinas:

1. A constant intrinsic state over a finite lifetime defeats the shortcut from
   within-life constancy to absence of a beginning or end.
2. Stable substantial existence with successive activities defeats the shortcut
   from substantial stability to proper eternity.
3. Unbounded successive motion defeats the shortcut from no beginning or end to
   proper eternity.
4. An internally stable aeviternal subject dependent on external conservation
   defeats the shortcut from internal all-at-once duration to independence.
5. A new duration structure satisfying chosen marks while primitive
   `Eternal = False` exposes the missing recognition commitment. It is not a
   historical or theological counterworld.

Do not eliminate these controls through a convenient lifetime type or an
assumption that every observation exists. A flags-only decomposition would be a
transcription. The candidate keeps A–C open until their source readings and
actual structure support a derivation.

## Existential inertia: the live rival and the remaining bridge

The complete author-published articles `SCHMID-INERTIA-REPLY-3-ARTICLE`
(Joseph C. Schmid, 7 July 2021) and `FESER-INERTIA-REPLY-2021-ARTICLE`
(Edward Feser, 6 July 2021) were pinned, materialized and read, excluding reader
comments. Their passage records locate the exact consulted bytes. These are
primary evidence of each author's position, not independent verification of
metaphysical adequacy. Feser's witness is the author-published Blogger Atom
entry: `source_evidence.py materialize FESER-INERTIA-REPLY-2021-ARTICLE`
returns its pinned XML, whose Atom `content` element contains the complete
article HTML. Its rendered text was reread and exactly matches the earlier
article witness; the final file newline is the only serialization difference.
The rendered webpage failed raw-byte verification in CI run `40776675501`;
the old expected/observed hashes are retained in the passage manifest. The
local narrow refetch still returned the original webpage bytes, so it cannot
establish the content of CI's differing response. Two independent Atom fetches
agreed; raw-byte verification remains enforced on the replacement endpoint.
Schmid's journal PDF and current-domain article returned
HTTP 403 to the evidence fetcher; the original author-published WordPress article
was accessible. No journal-paper reading is claimed.

**Rival replacement.** Schmid's paragraphs beginning “For S to fail to exist at
m” and “Here, we seem to have” explain persistence through earlier existence,
absence of a factor causing cessation, and a causal requirement on change. His
closing edit, paragraph beginning “And this discovery especially helps”, accepts
a PSR or PSR-like explanatory principle while disputing the identification of
extrinsic explanation with a sustaining cause. Thus the strongest rival here
is not simply unexplained persistence. Its proposed explanation can include
facts extrinsic to the object at the later time without a concurrent sustaining
efficient cause. Its sufficiency remains disputed. Laws, transtemporal relations
and propositional necessity are further accounts he mentions, not accounts
independently inspected in their linked documents.

**Strongest response in the inspected Feser article.** Under “EIT versus EET”,
the paragraph beginning “Rather, a critique” argues that constituents considered
just as constituents are only potentially the whole at the selected time;
past combination does not suffice to actualize their present combination.
Under “The metaphysics of existential inertia”, the paragraphs beginning
“Now, an objection” and “I find this” argue that a persistence power depends
ontologically on its substance, so the substance cannot depend on that same
power without circularity. The paragraph beginning “Schmid does not attribute”
explicitly allows past events a role in present explanation: the issue is their
sufficiency, not their relevance. Under “An argument against EIT”, paragraphs
beginning “Another problem” and “But this simply ignores” apply the circularity
and present-actualization objections to a proposed emergent persistence power
and the earlier-parts response. This response needs the concurrent-actualization
and dependence-direction premises; it does not follow from the mere fact that
a thing has persisted. Nor does its intrinsic-power criticism by itself answer
every law-based or extrinsic no-change account.

Feser's paragraph beginning “This makes it sound” expressly rejects annihilation
and recreation at every moment. This agrees with q.104 a.1 ad 4's distinction
between continuing esse-giving and a succession of new productions. It blocks
a diachronic-identity objection aimed only at repeated recreation. It does not
establish that conservation occurs.

**What q.104 contributes.** Objection 1 argues from naturally inseparable form
to no need for preservation; ad 1 makes the form's resulting esse conditional
on divine influence. Objection 2 invokes the house and heated water after their
agents cease; the response and ad 2 distinguish causes of becoming from causes
of being. Objection 3 infers persistence from absence of corruption; ad 3 limits
this to preservation against corruption. Objection 4 challenges a preserving
action that adds nothing new; ad 4 answers with continuation of the giving of
esse. The response's paragraph beginning “Now every creature may be compared”
applies the illumination analogy through participated esse and essence–esse
distinction. These are articulated reasons and replies, but their application
to every creature remains a substantive dependence commitment. Treating the
illumination comparison as independently proving all existential dependence
would hide the disputed bridge.

| Existing typed commitment | What this reading establishes about the rival |
|---|---|
| `STMT-BECOMING-CAUSE-NEED-NOT-SUSTAIN-BEING` | Persistence after a maker stops is compatible with both accounts. It does not discriminate them. |
| `STMT-EXISTING-IN-ACT-AT` | The rival does not settle the interpretation from modeled existence into the supplied `InAct`/`esse`. |
| `STMT-UNITING-CAUSES-PRESENT` | The rival does not assert an absent concurrent conserver. Whether a past explanatory factor counts as a typed `CausesIn` cause is precisely unresolved. |
| `STMT-ACTUAL-ESSE-CAUSES-SUPPORT-AT` | A conditional map of already-given actual esse causes can hold even if no such cause is supplied for the persisting object. It does not generate conservation. |
| `STMT-Q3A4-DISTINCT-ESSE-CAUSE-DICHOTOMY` | A noncausal persistence explanation contests causal exhaustiveness only if the same target has the represented distinct essence/esse and lacks both efficient-causal disjuncts. Schmid's article does not fix those assignments; no formal denial is attributed. |

The exact interface types are in `TruthCore/Causality/ExistenceActuality.lean`
and `TruthCore/Causality/UnderivedNonComposite.lean`. The existing theorem
`TruthCore.Results.Causality.UnderivedEssenceEsse.actual_not_not_identity_direct`
requires an actual named target, no incoming support, actuality, cause presence,
typed correspondence, q.3 causal exhaustiveness and efficient self-cause
exclusion. Its constructive conclusion is **double-negated** represented
esse–essence identity. It supplies neither a conserver nor the truth of any
interface. No new theorem or finite graph is needed to rediscover those limits.

Two scope checks matter before formalizing the rival argument. First, from
cessation implying a destructive cause and absence of that cause, one obtains
non-cessation; if cessation is encoded as negated later existence, positive
later existence additionally needs stability/double-negation elimination.
This is an encoding diagnostic, not a claim that Schmid adopts constructive
logic. Second, a pointwise conserving cause `∀ t, ∃ c, ...` is not one fixed
conserver `∃ c, ∀ t, ...`; neither statement identifies that conserver with the
same root witness. Times in an inertia account are not automatically worlds
in `Ontic`, and q.104's timeless action is not automatically a temporal sequence.

The next discriminating obligation is to defend or reject the sufficiency of
prior existence plus no destructive change for the **same** existing bearer,
against the proposed need for concurrent actualization. Separately defend the
interpretation from direct conservation into `CausesIn ... esse`, endpoint
presence and its map to `R`. Efficient cause, ontological dependence, adequate
reason and preventing corruption retain separate meanings. No premise was
added to an argument, discharged or removed; root-route open premises are
unchanged. This reading narrows the rival and the missing bridge, without
advertising a new proof or an elimination of existential inertia.
