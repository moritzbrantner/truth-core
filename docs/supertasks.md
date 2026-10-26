# Supertasks: can an endless task finish?

**Question.** A *supertask* is commonly proposed as a sequence of infinitely
many distinct operations carried out during a finite interval. An objection
is that an **endless task cannot end**. That slogan has at least two meanings:

1. An endless, naturally indexed sequence has **no last operation**.
2. Such a sequence cannot have a **terminal time or well-defined result**.

The first is true of an omega-ordered sequence. The inference to the second
needs a separate premise: for example, **every actually completed task has a
last constitutive operation**. We should investigate and defend or refute
that principle, not conceal it in the definition of *completed*.

## Mathematical controls

| Example | Mathematical outcome | What follows, and what does not |
| --- | --- | --- |
| Geometrically shortening durations, $\sum_{k=1}^{\infty}2^{-k}$ | The ordinary partial sums $s_n=1-2^{-n}$ approach **1**. No stage is last; all stage times are before the endpoint. | A *finite-time schedule* and an abstract limit are mathematically coherent. Physical execution, causal completion and a particular endpoint state are not thereby established. |
| Uniform positive duration, $1+1+1+\cdots$ | Partial sums are $n$ and are unbounded. | With a fixed positive minimum duration per operation, an omega sequence cannot fit into a finite duration budget. **The cost assumption matters.** |
| Alternating unit changes, $1-1+1-1+\cdots$ | Ordinary partial sums alternate between 1 and 0 and have **no ordinary limit**. | An endpoint state need not be defined by the preceding values. Generalized summation methods are separate conventions, not ordinary convergence. |
| A constant or eventually constant Boolean output after each stage | The output has a stable terminal value. | No **last indexed operation** is necessary for a well-defined *abstract* limit value under the specified semantics. |

Mathematicians do not reject divergent series as ill-formed objects; they
reject assigning them a **finite sum in the ordinary sense** when that sum
does not converge. Likewise, the existence of infinitely many terms does not
by itself imply divergence. The decisive properties are the durations,
partial sums and terminal-state rule.

The distinction between an actually performed sequence of discrete operations
and a continuum that is indefinitely *divisible* also matters. Traversing a
distance does not automatically instantiate one separately caused action per
mathematical subinterval. Compare Aristotle's already sourced discussion in
*Physics* VI.2 (`STMT-ZENO-TRAVERSAL-CONFLATES-INFINITY-SENSES`).

## Three formal results

The Lean module `TruthCore.Causality.Supertasks` defines a small, explicit
model. It deliberately uses a distinct limit-order point, not a physical
clock. Each result has a separate Challenge, Solution, inference application,
argument and Comparator record.

1. **`SUPERTASK-STABLE-ENDPOINT`:** All natural-number-indexed stages precede
   a designated endpoint, every stage has a later stage, and a constant
   Boolean output has a stable terminal value. This defeats the *bare logical*
   inference **no last stage => no abstract endpoint with coherent output**.
   It is **not** yet a proof of a realizable finite-time supertask.
2. **`SUPERTASK-OSCILLATION-NO-STABLE-LIMIT`:** A recursively alternating
   Boolean output cannot be eventually stable at any proposed terminal
   value. The endpoint may be adjoined as an order point without solving the
   terminal-output problem. This is a discrete analogue of Thomson's lamp;
   no historical attribution is recorded without a pinned source witness.
3. **`SUPERTASK-UNIT-COST-UNBOUNDED`:** The partial cost of $n$ unit-duration
   stages is exactly $n$, so every finite budget is exceeded by some prefix.
   It establishes a *conditional impossibility* for a fixed-positive-cost
   schedule, not an impossibility result for all omega sequences.

The convergent geometric sum and oscillating numerical series above are
mathematical **illustrations**, not additional Lean-verified limit theorems.
The first Lean model proves order-plus-stability coherence only; it does not
encode metric convergence of the geometric series. Nor does an eventually
stable Boolean terminal value supply a physical mechanism for attaining it.

## Strongest objection and strongest reply

**Objection (completion principle).** To *finish* a genuine task is to perform
its final constitutive act. But an omega-sequence of discrete acts has no
final indexed act. Therefore an omega-sequence cannot be *actually finished*.
The apparent limit at time 1 is at most a mathematical idealization; calling
it *completion* would assume exactly what the argument contests. If physical
operations require nonzero lower-bounded time, energy or causal resources,
the divergent-series case provides a further conditional barrier.

**Reply (limit completion).** A process can be specified through all of its
stages and an additional endpoint without any last stage. Convergent partial
sums show that the mere absence of a final term is not a mathematical
contradiction, and a stable observable output can have a coherent limiting
value. The objection must justify why *actual* completion requires a final
constitutive act, or why the necessary acceleration/resource demands are
impossible. Neither is established by the natural-number order alone.

**Surviving dispute.** Is this a sequence of genuinely separate performed
causal operations, or only a mathematical subdivision or description of one
continuous process? Can an endpoint state be actual without a last producing
event? Does an adequate explanation require a source beyond local operations?
Those are philosophical and potentially empirical premises. Keep an objection
alive when its strongest coherent opponent model survives.

## Connection to the causal-regress frontier

- [Grim Reaper analysis](causal-regress-and-grim-reapers.md) establishes an
  inconsistency from a **special firing rule** plus an unbounded deadline
  order. The inconsistent rule is not supplied by every supertask.
- **#310 (actuality)** asks whether simultaneous *per se*, essentially
  borrowed causal power can be active without an intrinsic source. That is not
  the same question as whether an omega sequence of *temporal* operations can
  have a limit endpoint.
- **#311 (explanation)** asks whether an infinite set of local transfers can
  be explanatorily sufficient. A convergent temporal series neither provides
  an explanatory source nor refutes one; mathematical convergence and
  metaphysical grounding must not be conflated.

The open bridges are: **SU-END** (must a completed causal task have a last
operation?), **SU-REAL** (can an omega sequence of distinct physical acts fit
in finite actual time?), **SU-OUTPUT** (which terminal-state semantics are
defensible?), and **SU-GROUND** (if such a sequence is coherent, what causes
or explains its actual completion?). None is closed by the three formal
controls above, and none presupposes Thomism.
