# Koons's 2022 Fourth Way reconstruction

Primary witness: `KOONS-FOURTH-WAY-RECONSTRUCTION-2022-FULL-ITEM`, the
author-linked RSS item for [A Further Reconstruction of the Fourth
Way](https://robkoons.net/old-blog-2021-22/a-further-reconstruction-of-the-fourth-way),
published 23 January 2022. Initial witness acquisition added no claim.
The subsequent reviewed profile records only the restricted step 7 and
guarded step 11 readings described below.

## Reading returned for interpretation review

Steps 1–5 concern possible things and a **possible** maximum. Step 2 already
assumes comparison with such a possible standard; it is not a proof of an
actual maximum from bare gradation. Step 4 transfers maximal value to maximal
existence. Steps 6–13 import a necessary being **or plurality**, possible
universal causation in each world, a weak cause–effect degree bound, and
cross-world invariance of a necessary being's degree. The resulting
all-world maximum is conditional on that different modal/causal background.

The causal bound in step 7 is non-strict; it is not the repository's
unrestricted strict cause-more-such premise. A maximum relative to a world's
inhabitants and maximum possible existence also require separate treatment.
Plurality, transworld identity, domains and degree comparison are not silently
resolved by the post. Its closing concern specifically identifies step 5, the possible-maximum
conclusion, as potentially redundant; it does not simply remove step 4, which
is still cited at step 13 for maximum value. This is not the uniqueness
problem described in issue #345. No uniqueness conclusion
or direct discharge of `STMT-GRADES-HAVE-A-MAXIMUM` is warranted here.

## Witness and extraction boundary

The canonical HTML post is readable, but repeated fixed-User-Agent source
fetches changed their raw bytes. Comparing two responses isolated the change
to Cloudflare's per-request `r`/`t` script parameters; the selected post text
had the same SHA256. These responses were **not** normalized or admitted as a
stable source witness.

The page's actual RSS anchor is `/4/feed`; the adjacent `rel=alternate` link
has an empty `href`. Four normal source-tool fetches of
`https://robkoons.net/4/feed` gave identical response bytes:
`61854f98b4887ae9c5cbdea88f9fd1a83a4f1a318a0412dc6e058629ee1d9047`.
The existing `web_snapshot`/`raw_text` extractor preserves the UTF-8 XML
verbatim, including its CDATA, and materialization verifies those bytes.
The existing HTML heading/element selectors do not read this CDATA; no new
extractor was added.

The consulted item is uniquely identified by title, publication timestamp
`Sun, 23 Jan 2022 22:09:24 GMT`, and GUID/canonical link
`http://robkoons.net/old-blog-2021-22/a-further-reconstruction-of-the-fourth-way`.
Read its complete `content:encoded`, all thirteen numbered steps and both
closing paragraphs, from the **materialized** XML. Local XML/HTML decoding was
only a reading aid derived from that verified file; it did not replace the
snapshot, text hash or source-evidence extractor. The shorter RSS
`description` is not used as the argument witness.

Reproduction:

```bash
python3 scripts/source_evidence.py materialize KOONS-FOURTH-WAY-RECONSTRUCTION-2022-FULL-ITEM
```

No source text or feed bytes are committed. The feed can change in future;
without a matching fixed archive fallback this witness remains fragile.

## Rejected access approaches

- Canonical post URL: readable in this session, so issue #345's reported
  404 is no longer the present access state. The category URL
  `/old-blog-2021-22/category/fourth-way` returned 404 to browsing despite
  indexed results. Search snippets were orientation only.
- `www` and HTTP versions of the post redirect to the same volatile HTML.
  Its HTML advertises no print endpoint.
- Guessed `/1/feed`, `/old-blog-2021-22/1/feed` and
  `/old-blog-2021-22/rss.xml` failed. The author-linked `/4/feed` succeeded;
  `/old-blog-2021-22/feed` also served a feed but had a different channel
  publication timestamp and is not the pinned URL.
- HTTPS Wayback CDX and availability requests reset; HTTP availability
  returned 403. A request under the fixed path
  `https://web.archive.org/web/20260330150135id_/https://robkoons.net/old-blog-2021-22/a-further-reconstruction-of-the-fourth-way`
  also reset. This was an access probe, **not** a verified capture locator.
  The Arquivo.pt version-history query for the canonical URL reported zero
  captures. No archive timestamp or fallback hash is invented.
- A guessed `robkoons.weebly.com` version returned 404. No bibliographic
  fallback is needed or justified while a legitimate byte-pinned primary feed
  is available.

## Consequence boundary and next target

The current degree fork fixes one nonmodal contrast profile and strict causal
ascent. This reading instead motivates testing a modal weak-bound profile;
substituting one for the other would change premises. Compare the two blocks
under explicit world/domain/identity/degree semantics. The two restricted
source readings below do not source the remaining analyst background. Reuse existing statement identities only if their types
and meanings coincide. The witnessed unbounded branch has not been refuted by
this source reading, and no root premise closes.

## Validation

At source checkpoint `7aba445b78225b151b33ed4d584517cdc589a7d8`, offline source
and corpus checks passed. The normal
`source_evidence.py verify --base HEAD^ --head HEAD` command refetched and
verified the one newly added RSS passage with hash `61854f98b488`; the other
288 passages received offline checks only in that run. This verifies the
consulted feed bytes, not the argument or its interpretation.

## Proposed modal weak-bound profile: interpretation before claims

The proposed profile reuses the existing rigid-roster `Ontic` semantics and
keeps world-relative presence separate from a new preorder-valued degree
parameter. The degree parameter is an analyst's ordered intensity role, not a
count of worlds, a Boolean presence value, a proof of necessary existence, or
a supplied metaphysical analysis of esse. The post does not define a unique
numerical or order representation of existence degree. Neither a total order
nor antisymmetry is required by this proposal.

Step 7 supports considering a **restricted conditional** with both relata
present at the evaluation world, and with the effect's degree no greater than
the possible cause's degree there. Possible causation is represented using
existing accessibility and a supplied world-indexed cause relation. The
possibility witness can be a different world; the proposed comparison is
explicitly at the current evaluation world. Presence guards weaken the
unrestricted sentence. This reading does not infer that a possible causal
edge is actual, or that the supplied relation has adequate existence-causal
semantics without an independent interpretation.

Step 11 is recorded as a guarded selected-individual conditional: **if**
that individual is actually present at the standpoint **and** necessary in
the admitted-world semantics, its degree is equivalent to its reference-world
degree at each accessible world. Same degree is represented by mutual
non-strict comparison; distinct labels may be tied in a preorder.

The frozen main proof's bare `NecessaryDegreeInvariant` condition has only
necessary presence as antecedent. On a nonreflexive frame necessity need not
include base-world presence, so that predicate can constrain an absent
individual's base-world grade. Attribution of that stronger condition was
rejected. Claim 11 instead binds `ActualNecessaryDegreeInvariant`. The
separate adapter obtains actual presence from necessary presence plus actual
reflexivity, then composes the unchanged frozen main proof. No claim that
modal necessity alone fixes intensity, no necessary individual, and no
uniqueness are established.

Step 6 does not establish the proposed singular background. It permits a
plurality, and its literal wording does not omit the selected cause from
"all" existing things. Selecting one rigid individual, restricting targets
to others, and weakening collective possible causation into pointwise
possibility must remain explicit analyst choices. From the plural disjunct no
single necessary individual is inferred. No claim that the author has been
refuted by self-causation follows from analyzing an other-directed version.

The intended conclusion compares every accessible world's existent grades
with the selected individual's grade at **each** accessible world. That is
cross-world dominance, not merely local dominance inside one world. Explicit
actual reflexivity and necessary presence supply the actual-world witness;
the theorem must not promote vacuous universal bounds on an empty world
carrier into an actual maximum. The profile remains relative to its chosen
accessibility domain and does not establish a maximum across unrepresented
metaphysical possibilities or a unique maximal individual.

The possible-maximum/value-convertibility block, plural necessary sources,
and readings of literal universal versus other-directed causation remain
unformalized obligations in the existing comparison candidate. They are not
newly established premises, and no second research tracker is created.

## Independent profile and witness audit

The main proof derives a local weak bound and transports degrees through the
base-world grade using mutual inequalities. Its explicit excluded-middle
premise splits identity with the selected individual; it is not hidden in a
finite-model certificate. Actual reflexivity is only required at the base;
no S5, global reflexivity, transitivity or causal soundness is assumed. A
possible-cause witness need not lie in the root-accessible family when the
frame lacks transitivity; the bound nevertheless compares current-world
grades, exactly as its type states.

The five model profiles were inspected as joint interpretations, including
their presence, accessibility, causation and degree assignments. Tied necessary
maxima reject uniqueness, but do not establish a second universal causer.
Varying degrees retain local bounds and an attained global degree maximum
while refuting the named individual's maximum at every world. This does not
verify the source's entire steps 1–5 or the value bridge. The below-effect and
empty-cause controls separate the weak-bound and potential-cause commitments.
The potential-only profile satisfies the nonlogical background without any
base-world causal exercise. Generic excluded middle is an explicit logical
premise, not an additional fact certified by those finite interpretations.

The guarded adapter is an assembly/source-fidelity specialization, not a new
philosophical defense. Source 6 remains unattributed. Step 5 may be redundant
within the author's reconstruction; step 4's value/existence conversion is
still invoked at step 13 and is not discharged by these degree certificates.
Root-premise change: none. Final binding, Comparator and NanoDa checks belong
to the coordinator; this audit does not replace them.

## Mathematical refinement: attainment and an infinite residual

The local causal profile does not itself solve the maximum problem. Under
necessary presence, other-directed pointwise potential causation, weak
current-world bounds and explicit identity excluded middle, each existing
y at u satisfies grade(u,y) ≤ grade(u,N). Consequently an attained global
maximum exists exactly when N's own accessible-world degree family attains
a maximum. Forward, a globally greatest existing (v,y) is locally bounded
by (v,N); backward, an own-family greatest (v,N) bounds every existing
(u,y) by transitivity. Necessary presence supplies the witness's presence.
Neither actual reflexivity nor invariance is required. With no accessible
world, both existential attainment predicates are false. This is an exact
conditional reduction, not a defense of any maximum premise.

The frozen `UnboundedWorlds` control uses Nat worlds with universal
accessibility, the same source and first effect existing at every world,
and an actual source-to-effect edge at every world. Every individual's
grade at world k is k. Thus local weak bounds hold by reflexivity, while
any proposed attained global witness at k is exceeded by the existing source
at k+1. Both bare and actual-guarded invariance fail between worlds 0 and 1.
This is a single joint interpretation with actual causal exercise, stronger
than a residual relying on merely possible exercise. The frozen
`unboundedWorldControl` target was independently inspected before proof
completion; its Comparator/NanoDa delivery remains the coordinator's gate.

Invariance is sufficient but not necessary for attainment: the finite varying
degree control already has attainment without invariance. The infinite
control instead shows that the remaining local commitments cannot guarantee
attainment. Neither result prefers rejecting a specific premise, proves a
metaphysical possibility, or changes a root-path open premise. This refinement
uses the profile's explicit semantics without making a source attribution.

## Integrity follow-up: transient feed failure

Main revision `73dcbb13`, workflow run `40747604144`, job `123026416902`
failed at 18:53:52 UTC on 28 October 2026 with HTTP 404 for `/4/feed`.
Subsequent fresh requests using the production source verifier returned the
original 54,102 bytes and unchanged byte/text hash `61854f98b4887ae9c5cbdea88f9fd1a83a4f1a318a0412dc6e058629ee1d9047`.
Materialization in a fresh repair clone succeeded, as did an explicit
`materialize_web_snapshot(passage, use_cache=False)` verification of this
passage alone. Thus the endpoint recovered without a re-pin. The ignored
local cache also preserves the original witness; it is not a substitute for
network verification. No claim, locator, license or philosophical reading changed.

The publisher's `www` and HTTP feed variants returned the exact same bytes.
The alternative `/old-blog-2021-22/feed` returned different feed bytes and
was rejected as an exact-byte replacement. Wayback CDX returned `[]`, and
the availability API returned no archived snapshots. Save Page Now timed
out after 25 seconds; no successful capture or fixed fallback is asserted.
The source remains fragile against transient publisher failures. No source
manifest change can honestly guarantee its availability on another machine.
The existing materialization command above reproduces the focused boundary;
these findings do not justify marking the failed integrated CI run green.
Root-premise change: none.

The coordinator additionally confirmed hosted-CI recovery on integrated main
`a13fc469`: [run 40749570362, job 123032417241](https://github.com/moritzbrantner/truth-core/actions/runs/40749570362/job/123032417241)
passed the full source verification with unchanged witness inputs. The older
failed run is retained as failure evidence; no retry is needed to repeat the
new successful check.
