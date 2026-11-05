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

## Logic-first signed-cost reconstruction (#1034, 2026-11-05)

Attribution remains deferred under the owner's logic-first direction. The
following is a working reconstruction, not newly authenticated channel content,
Pascal interpretation, or source claim. No new source or passage is asserted.

`TruthCore.Decision.SignedWager` uses Mathlib `EReal`: real utilities include
negative finite costs, positive infinity, and negative infinity. Its partial
`add` returns `none` for either ordering of positive and negative infinity;
undefined expectation is never an ordinary zero or a candidate maximizer score.
`expectation p u v` uses complementary real weights `p` and `1-p`. A separately
stated `Probability` guard gives nonnegativity and normalization, rather than
pretending arbitrary algebraic weights are priors. Zero-probability outcomes
contribute zero, including an impossible infinite payoff.

The single-policy profile has independently selected act-one probability `q`
and policy-one prior `p`, success probability `p*q`, infinite utility on success,
and arbitrary signed finite utility `c` otherwise. The theorem permits every
real `c`, including negative expenses. Both probabilities are explicitly bounded;
positive `p` and `q` imply expectation `some top`. Thus finite costs do not by
themselves answer the strongest infinite-reward reply. This is a utility
consequence, not a premise that rewards actually exist or that expectation must
be maximized. The previous `InfiniteWager.mixtureTie` theorem is imported and
consumed as the old nonnegative control inside the certificate; that control is
not advertised as a newly discovered result.

The competing-policy profile has two incompatible rewarded acts: policy one
rewards act one and policy two rewards act two, each infinitely; failure has
finite utility `c`. Their priors are `p` and `1-p`, and the act lottery has
weights `q` and `1-q`. Independence yields success probability
`p*q+(1-p)*(1-q)`. This is proved to lie in [0,1]. If `0<p<1`, it is positive
for every feasible `q`, including both pure acts and every positive mixture.
All therefore attain top: expected value alone fails to single out one practice.
This is a symmetric reward-policy control, not a proof that every religion has
the same payoff, that all policies have positive priors, or that mixtures of
religious practice are feasible. The result allows asymmetric positive priors;
symmetry concerns the paired reward structure, not a mandated 50/50 prior.

Opposing *punishment* is separately tested: with strictly positive complementary
weights, expectation of positive infinity and negative infinity is `none`.
One must either restrict the utility domain, supply a different decision rule,
or justify a regularization/ordering before drawing a practical conclusion.
The guard deliberately does not accept Mathlib's totalized opposing-infinity
addition as decision-theoretic arithmetic. Setting prior or rewarded-act weight
to zero instead gives the finite outcome, so dropping positivity invalidates the
infinite-reward conclusion. Both zero controls are explicit model witnesses.

`practicalNontruth` gives an actual two-world model: prior 1/2, act-one weight
1, unsuccessful utility -1, and a religious proposition true only at the other
world. The actual world is false. Act one maximizes the single-policy expectation;
every feasible lottery maximizes the competing-policy expectation. Distinct
weights 1 and 1/2 tie in the signed profile. This witnesses why practical
maximization does not entail actuality of a religious proposition. Neither
`Maximizes` nor an act lottery represents choosing a belief; belief control is
not derived. Zero-prior and zero-action alternatives in this same negative-cost
model fail to attain top, making the omissions nonvacuous.

Scope and strongest replies: tie-permitting maximizing norms survive, and an
explicit tie-breaking norm could select an act. A theological argument could
exclude a rival policy or assign a zero prior; that is an additional commitment,
not a decision-theoretic consequence. A finite/truncated utility model might rank
acts differently; this theorem assumes genuinely infinite rewards. State/action
independence, shared finite failure utility, feasibility of lotteries, payoff
assignments, priors, and any practical norm remain application assumptions. The
profile does not yet model distinct finite costs in every outcome cell, an
arbitrary finite family of religions, correlated policies/acts, or a defended
salvation theory. These limits do not turn the formal conditional into a source
reading or a truth-root proof.

Claim/type self-sweep: two structured mathematical certificates, no opaque-Prop
transcription and no added theological axiom. The only actual-world countermodel
is the explicitly defined Bool interpretation; it does not refute religious
truth. No new stating claim, source, passage, or root-support edge is created.
No premise is defended, added to the truth root, removed, or discharged.
The conditional work connects signed utility arithmetic with a practical
nontruth control; frontier/root-premise delta is none.

Frozen Challenge SHA256:
`d419888370e41bd902f64d7de0bf4e978b7187a1984e00f97b2f5903c5d7f1cb`.
Its typed vocabulary snapshot SHA256 is
`c1a0dcd0ca0921f6ff46532e2b5097b6698c78b84f48790c69f5c2a1bda2afe3`.
Shared convention sourceRevision:
`625cb04ca568aebc8d45c90033e107a05e9bd2a0`.
