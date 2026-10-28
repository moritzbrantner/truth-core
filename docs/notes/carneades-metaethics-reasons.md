# Carneades: reasons, factual information, and plans

This bounded investigation tests the reasons objection in Carneades.org's
*What is Emotivism? (Philosophical Definition) The Boo-Yay Theory*,
https://www.youtube.com/watch?v=39uOXZVVHoA . It does not attribute the formal
semantics below to the channel, Hume, Blackburn, or Gibbard. The downstream
purpose is to discriminate an inferential objection from the stronger demand
for categorical normative warrant, while retaining sophisticated expressivism
and cognitivism as live rivals. No Catholic root connection is asserted.

## Actual reading and source boundary

Read the complete English `en-orig` automatic captions, 00:00–05:03, downloaded
2026-10-28 with the installed `yt-dlp`; metadata identifies Carneades.org as the
channel. Raw VTT SHA256:
`d36d2efa49fad2b298e1fba1bdaaec1a43287848c95c3e6053d51f808d5b2b0b`.
Reproduce acquisition with:

```sh
yt-dlp --skip-download --write-auto-subs --sub-langs en-orig \
  --sub-format vtt --write-info-json --socket-timeout 15 --retries 0 \
  --output '/tmp/carneades-metaethics.%(id)s.%(ext)s' \
  'https://www.youtube.com/watch?v=39uOXZVVHoA'
```

This is provisional reading evidence, not a pinned passage: automatic caption
errors occur, audio/slides were not checked, and the hash is not a materialized
`media_span` hash. No attributed corpus claim is created. A future attribution
requires the existing media-span provenance/materialization process and checks
of decisive audio wording. No full copyrighted transcript is committed.

The argument, read in the whole recording's context:

- **00:13–01:12:** distinguishes normative ethical judgments from metaethical
  explanation of what good/bad language means.
- **01:12–02:34:** presents emotivism as approval/disapproval, and extends a
  denial of truth/falsity to noncognitivist theories generally. This broad
  extension is not adopted: the corpus already preserves minimal-truth
  expressivist replies.
- **02:34–03:54:** discusses descriptive and expressive components of thick
  terms through bravery/brashness and fearlessness. This is a proposed
  decomposition, not a demonstrated exhaustive semantics of thick concepts.
- **03:54–04:49:** objects that condemning murder seems to demand more than
  expressing distaste. Contrasts reasons for preventing murder with merely
  disliking someone's bright-green living room, and argues that without
  statements of truth/falsity the emotivist cannot give reasons beyond dislike.
- **04:49–05:03:** closes by asking whether moral claims are only attitudes or
  true/false claims. This question supplies no premise establishing realism.

The decisive missing bridge is between *absence of robust descriptive moral
truth* and *absence of any structured reason-responsive practical inference*.
The latter does not follow merely from the former's verbal description.
Conversely, a material-support model with valid inference does not establish
categorical normative authority or an adequate psychological explanation.

## Reuse and strongest replies

Dossiers inspected: `STMT-PLAN-STATE-EMBEDDING-CONTROL` and
`STMT-EXPRESSIVISM-CONSISTENT-WITH-GEACH-VALIDITY`.
Existing `TruthCore.Metaethics.PlanStateEmbedding` provides the exact Point,
Sentence, support, and Accepts definitions. Its factual field and permission
field stay distinct. The exact theorem reused is
`TruthCore.Results.Metaethics.PlanStateEmbeddingControl.planStateEmbeddingControl`;
its first conjunct proves general acceptance-preserving MP. The earlier
primitive-ValidMP/Unit-sentence consistency control is not reproved. Searches
for existing Hume/is-ought, factual invariance, and conservative-fragment results
found no existing theorem establishing the new structural factual-fragment
property in this grammar. Existing self-application/retorsion controls concern
accurate performances and presupposition links, not this practical inference;
no performed-denial bridge is assumed here.

**Strongest expressivist reply retained:** a noncognitive account can posit
structured plans, factual sensitivity and inferential relations, potentially
including minimal truth. It need not reduce each utterance to an isolated
emotion or require every conditional occurrence to perform the same expression.
The present conditional-support reconstruction is one explicit test, not an
attribution or a sufficient metasemantic explanation.

**Strongest cognitivist reply retained:** preserving inferences under a
stipulated support clause does not explain why practical commitments have
logical rather than merely pragmatic incompatibility, why an agent ought to
accept a plan, or whether the account captures ordinary moral thought. A demand
for categorical normative warrant may survive all the present controls. Moral
realism itself is not inferred; cognitivists can also accept a fact/value gap,
and a defended naturalistic identification may dispute our syntactic partition.

Rejected readings: treating “I approve” as unambiguously a descriptive report
rather than expressive shorthand; equating all noncognitivism with denial of
minimal truth; conflating any Boolean semantic representation with robust
mind-independent moral fact; treating the murder/paint contrast as a proof
of categorical moral truth; repeating the existing naive-emotivism refutation;
and identifying material support with Gibbard's historical indicative semantics.
The latter mismatch is documented in `docs/expressivist-embedding-boundary.md`.

## Formal test and exact boundary

`STMT-DESCRIPTIVE-PLAN-BOUNDARY`, result `DESCRIPTIVE-PLAN-BOUNDARY`, binds
`TruthCore.Results.Metaethics.DescriptivePlanBoundary.boundary`.

1. `Descriptive` restricts the existing grammar to factual atoms and recursively
   factual conditionals: no forbidden-action atom occurs at any depth.
2. Structural induction proves support of such a formula invariant under
   changing only a point's permission plan. Conditional cases recurse through
   both sides, including negative antecedent occurrences.
3. For any set of descriptive premises with a supporting point, replace its
   plan by the all-permitting plan. Every premise remains supported. Thus the
   theory has a point that excludes no action. This is **semantic
   non-entailment** of any forbidden-action atom; no proof calculus or soundness
   theorem is supplied, so no syntactic nonderivability claim is made.
4. Reuse the existing general MP theorem to obtain acceptance of a forbidden
   atom from acceptance of a factual atom and its factual-to-forbidden
   conditional. This conjunct is composition of an existing result, not a new
   discovery or defense of the normative conditional.
5. An inhabited singleton state permits all actions and accepts the factual
   atom, but accepts neither the selected prohibition nor that conditional.
   Abstention remains permitted in every point. This explicit omission control
   rules out empty-state vacuity and shows why factual guidance is conditional.

The statement has no external proposition hypotheses. Its universal
satisfiability condition is internal and explicit, so inconsistent factual
premises do not purport to yield a countermodel. Arbitrary Fact/Action carriers
are allowed in the universal property; the omission control uses Unit facts
and the existing three-constructor action type. No existence of actual agents,
murder, categorical reasons, or moral truths is inferred. The new unrestricted
all-permitting completion depends on the existing independent fields; adding
cross-field coherence requirements could block that construction and would
require a separately justified semantic revision. A noncognitivist need not
accept all-permitting plans as morally good for them to be semantic points.

## Evidence and premise comparison

The local shared service accepted the combined definition and proof text at
preview HEAD `49b4589aa6744c91a6bc9adec13215d0e7245c9d`, workspace
`/home/brantner/privat/truth-core-sprint-proof`, session `causal-harvest`,
path `Scratch/carneades-metaethics/Boundary.lean`, submitted-content SHA256
`985b1cf0e51e8bc455a66acd2d3cc727021ba68feb691128d84d7e2e3e12b63a`.
The response contained no errors and printed zero axioms. This is interactive
elaboration evidence, not final build/binding/Comparator/NanoDa certification;
canonical final CI remains authoritative. Corpus record and source-evidence
manifest checks pass; generated import/doc indexes are current. Both frontier
`--routes` and `--reaching-root` reports were byte-identical with versus
without the new corpus batch.

Intended and actual premise delta: **no change** to existing theories, answers,
root routes or open premises. The stipulations added are a syntactic fragment
predicate and named properties of unchanged semantics; the theorem connects
existing semantics and MP through structural invariance. It discharges no
historical, psychological, semantic-adequacy or categorical-warrant obligation.
The existing candidate `EXPRESSIVIST-LOGIC-OF-ATTITUDES-COST` remains open for
that adequacy gap; caption acquisition is not its primary-witness fulfillment.
The attempt record is `ATTEMPT-CARNEADES-METAETHICS-REASONS`.
