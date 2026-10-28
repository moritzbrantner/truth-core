# Carneades electoral aggregation diagnostic

Owner-authorized broader Carneades research, 2026-10-28. Independent mathematical
test `POLITICAL-DISTRICT-MAJORITY-CONTROLS`; no root premise change.

## Consulted reading and evidence boundary

Read the complete English `en-orig` auto-caption stream of **What is Democracy?
(Philosophical Definition)**, Carneades.org,
https://www.youtube.com/watch?v=HlONC5qbXds . Metadata duration: 486 seconds;
spoken caption stream consulted from 00:00 to 07:56. Public access only, no
login, enrollment or payment. Reproduction:

```sh
yt-dlp --skip-download --write-auto-subs --sub-langs en-orig \
  --sub-format vtt --write-info-json --socket-timeout 15 --retries 0 \
  --output '/tmp/carneades-political.%(id)s.%(ext)s' \
  'https://www.youtube.com/watch?v=HlONC5qbXds'
```

Consulted VTT SHA256:
`2e5d4c0312b01b1b582ebbc232e57a2aa631dc68a87124d1cb744820ea1cf1de`.
This identifies a downloaded caption file, not an authenticated `media_span`
export or `span_sha256`. Audio and slides were not checked. Captions have obvious
word-recognition errors. All readings below are provisional descriptions of the
channel narrator, not authenticated historical attribution or a source claim.
No copyrighted transcript is committed. Before creating an attributed corpus
claim, obtain existing media-span producer/export provenance, materialize the
pinned passage, and check decisive words against audio.

- **00:20–01:28:** distinguishes basic rule by the people from disputes over
  implementation and governments' self-descriptions.
- **01:28–02:33:** describes electoral, liberal, participatory, deliberative,
  and egalitarian variants. Reject treating this as proof of a necessary linear
  ranking: the caption says six while apparently listing five, and no V-Dem
  primary documentation was consulted. Nothing in the formal result uses it.
- **02:33–04:08:** argues that different ideas of good governance add different
  demands to democracy; practical responsiveness depends on implementation.
- **04:08–04:48:** distinguishes periodic voting from meaningful competition,
  citing no opposition, parties controlled by one group, and gerrymandered
  districts. This is the motivating omission question: what does having an
  equally counted ballot guarantee about the aggregate result?
- **04:50–05:07:** points to Arrow and Downs companion discussions. This
  investigation does not claim to have read those companions or prove Arrow.
- **05:08–05:53:** historical criticism attributed to Plato and Aristotle;
  rejected as evidence for their actual positions without primary witnesses.
- **05:53–06:41:** presents speed-of-decision criticism and a reply concerning
  deliberation's longer-term benefits. Neither empirical comparison was tested.
- **06:43–07:21:** connects unequal wealth to cost-benefit analysis and promotes
  a book. No purchase; no inference from money to formal vote weights here.
- **07:25–07:56:** closing discussion invitation and channel notices.

## Independent formal question, strongest rivals and controls

The actual conditional question is whether equally counted ballots and equal
numbers of voters per district force agreement between the popular majority and
a majority of district winners. The encoded answer is no: in a nine-voter,
two-party fixture, A's district counts 3,1,1 give five votes but only one district.
The alternative 2,2,1 gives the same five total votes and two districts. Both
profiles keep three voters per district. The theorem also proves universal
unanimity controls for A and B. These are computed finite witnesses plus a
universal argument, not an opaque obligation proposition assumed as a bridge.

This is an omission test of an electoral inference, not a democratic legitimacy
criterion. A territorial-representation defender can accept the arithmetic and
prefer district representation. A proportionality defender can prefer direct
population aggregation. Neither normative standard is decided by the model.
The profiles preserve A/B multiplicities; the model does not encode geographical
contiguity, legal redistricting, strategic intent, turnout, or stable named voter
identities. Equal input weights are not a theorem about equal political influence.

For the original obligation question, the strongest consent rival requires an
actual voluntary authorization rather than mere participation or winning. A
natural-duty rival may justify some obligations independently of consent; an
anarchist rival may deny a general duty while accepting particular moral duties.
All remain open. Majority reversal neither refutes political authority nor
proves that no individual consented. Conversely, fixing the reversal would not
establish consent or obligation. No church/state authority identification is made.

## Reuse, proof boundary and premise comparison

Searched existing `TruthCore/` and corpus definition records for political,
consent and voting vocabulary; found no matching electoral profile. Existing
church or causal authority concepts do not have the same meaning. Reuse standard
`Fin`, `Bool`, `Nat`, arithmetic and Mathlib tactics; no external dependency or
new proof-status machinery. The fixed three-element sum is an explicit finite
count, not a replacement for a general mathematical theory of elections.

Certificate type has no external premises. Normative truth and real-world
applicability are not hidden hypotheses: no such conclusion is asserted. Intended
and actual root-path open-premise delta: zero added, zero removed, zero
discharged. The new statement is outside every Catholicism root route. The
statement dossier was inspected after creation; source readings remain empty.
The mathematical fixture is new work; the provisional caption reading is
orientation only. No philosophical proposition is created merely to log activity.

## Comparator repair boundary

Initial PR #643 head `693cab84` passed corpus/build and library checks, but the
result Comparator rejected a private `Nat.add_le_add_left.match_1_1` type in the
`simp`-generated unanimity proof. The repair rewrites each unanimous function to
the corresponding constant profile using extensionality and computes the finite
result with `decide`. It does not modify the frozen Challenge or certificate.
Shared-session preview at HEAD `f2db33e8273b214f158d63e2e3a17094ba181735`,
content SHA256 `af1c5e73da24eb3fef3213ea81d352ae37b206be4887875e1fc15548b41500e7`,
returned no Lean diagnostics. Final Comparator certification remains distinct
from this interactive result; see PR checks for the delivered head.
