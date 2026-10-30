# Carneades wager intake and restricted mixture control

## Public reading

Read the complete English automatic-caption stream of Carneades.org,
[Pascal's Wager](https://www.youtube.com/watch?v=p3ScupIbdkU), 00:00–06:24,
on 2026-10-28. Channel search metadata identifies channel
UC1VzCyqpmCaRh8_BnijbOvg. The existing yt-dlp installation downloaded the VTT
without authentication or a media download. Audio and slides were not inspected.
Automatic recognition is visibly imperfect. This is a provisional caption
reading, not a materialized corpus witness or a historical Pascal claim.

Precise useful spans, paraphrased:

- 00:18–00:43: the presenter explicitly offers a charitable reconstruction,
  rather than an exact presentation of Pascal, and promises stronger objections.
- 01:01–01:33: practical profitability is distinguished from a standard argument
  for God's existence, although the introduction calls the wager an argument
  for existence. Preserve that tension rather than inferring theoretical truth.
- 01:34–02:08: decision-matrix procedure weights each outcome and adds values.
- 02:13–03:26: illustrative 50/50 game, reward 3 and loss 1, versus abstention.
  Captions report expectation 0.5; the stated arithmetic is actually 1.
  Whether this is a spoken error or caption error is unverified. Source
  arithmetic is not a proof oracle and this detail is not formalized as fact.
- 03:33–04:51: reconstructed religious matrix gives infinite reward in the
  rewarded belief branch, finite bad elsewhere, and finite good for the
  nonbelief/no-God branch. It expressly concedes nonzero finite costs.
- 04:52–05:50: an arbitrarily small positive prior is said to retain an infinite
  expected advantage over wholly finite alternatives.
- 05:54–06:24: many-gods and doxastic-voluntarism objections are announced;
  this video does not develop them.

The companion [Objections to Pascal's Wager](https://www.youtube.com/watch?v=ACeOPJPsHd8)
was identified as the same channel, duration 267 seconds. Its automatic-caption
request returned HTTP 429. Its content was **not read**; no objections are
attributed to it. No repeated access workaround was attempted.

## Independent mathematical control

`TruthCore.Decision.InfiniteWager` deliberately uses Mathlib `ENNReal`, a
nonnegative extended value space. The reward-state prior is `p`, and an
independent mixed act selects the rewarded option with probability `q`. Reward
is top on success and zero otherwise, so expectation is `p*q*top`. All
other contributions vanish. Mathematical weights may exceed one in the
universal algebraic theorem; actual prior/mixture interpretations restrict
weights to [0,1]. The concrete alternatives one and one-half are probabilities.

The strongest pragmatic reply to finite-cost objections is exactly why an
infinite reward was selected. The new control instead tests strict ranking:
all positive mixtures tie at top with pure selection. Under this coarse expected
value alone, the pure act has no strict advantage over every distinct mixture.
This does not refute maximizing rules that permit ties, add a tie-breaking rule,
establish any duty to randomize, or support belief voluntarism. The zero-prior
and zero-action controls show why nonzero factors matter.

Rejected readings: (1) this ENNReal profile proves that signed finite expenses
never matter—false scope, since ENNReal cannot represent negative utility;
(2) numerical expectation proves a religious proposition—there is no world-truth
predicate or inference of that kind; (3) choice of act is choice of belief—no
belief states or doxastic agency are encoded; (4) the charitable reconstruction
is Pascal's historically exact argument—the speaker explicitly disclaims that.

Remaining gaps: pinned media provenance and materialization for attribution;
signed-cost treatment with an appropriate extended value space; opposing
infinite stakes; many-gods alternatives; feasibility of mixed religious acts;
practical maximizing and tie-breaking norms; empirical/theological priors and
payoffs. These are open application commitments, not discharged premises.
The control is separate from #375/#376's unimplemented practical roots and has
no edge to the Catholicism truth root. Root-premise delta: none.

## Development evidence

Challenge frozen before proof at SHA256
`c71299b3afe52b28e7ad43c1a278f5d71901393ff2a563c23fcac4976e6a0cd7`.
The coordinator-owned local Lean session checks the full submitted source,
not final canonical module packaging; final CI remains authoritative.

Downloaded VTT SHA256:
`1261d570c5cb672073011753d4c42bf0b812f50a016d5ba79bc65088c1367986`.
This download hash records what was read and is not a pinned corpus witness.

Accepted shared-session full-content submission: workspace
`/home/brantner/privat/truth-core-sprint-proof`, HEAD
`49b4589aa6744c91a6bc9adec13215d0e7245c9d`, session `causal-harvest`,
path `Scratch/carneades-decision.lean`, version 3, SHA256
`5c59ba75add11a4a42a5b719d972aca918acc6880495fb70bb9c463c4477c8e0`,
empty diagnostics. The preview was dirty and the API bound the exact submitted
content; no final CI or Comparator status is inferred from this observation.
The first probe required a noncomputable marker and the current Mathlib import;
the second accepted the proof with a cosmetic linter warning, removed in v3.
