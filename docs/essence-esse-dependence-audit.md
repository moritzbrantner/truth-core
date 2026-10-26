# Essence and esse: the causal dependence argument under alternative explanations

This slice advances #319 (with #312 and #275 as separate inputs) by
formalizing **the first proof in Aquinas, ST I q.3 a.4**, without assuming
Thomism, an unrestricted PSR, or the existence of God.

## Verified sources and exact scope

- **Aquinas, ST I q.3 a.4 co. (first proof),** pinned Latin passage
  `AQUINAS-ST-I-Q3-A4`: `si igitur ipsum esse rei sit aliud ab eius
  essentia` introduces two causal options: `a principiis essentialibus` or
  `ab aliquo exteriori`; the next sentence excludes sufficient causation
  of one's own caused esse by one's essential principles. The conclusion
  is *caused by another*. This article also gives distinct act/potency and
  participation arguments; the present slice does **not** combine them.
- **Aquinas, ST I q.104 a.1**, pinned English witness
  `AQUINAS-ST-I-Q104-A1-EN`: a cause of a thing's *becoming* need not be
  a cause of its *being*, and direct preservation of being is not simply
  preventing corruption. This warns against substituting the transfer of
  an arbitrary causal exercise for the cause of esse.
- **Leibniz, *Monadology* §§32–38 and 45**, pinned translation
  `LEIBNIZ-MONADOLOGY-31-45`: his PSR requires reasons for true facts;
  necessary truths may have reasons via analysis; he considers an infinite
  contingent series insufficient as its own complete reason; and in §45
  asserts that the necessary being has the reason for its existence in
  itself. These are source claims, not adopted axioms here.

## Actual dependency of the first proof

For a subject `x` that is **in act at esse** and whose represented essence
and esse differ, we keep two *source-derived but open* principles:

1. **Causal exhaustiveness:** `x`'s esse is caused either by `x`'s
   essential principles alone sufficiently or by another existing agent efficiently causing
   `x` in the `esse` respect.
2. **No essential efficient self-cause:** the essential principles do not
   sufficiently efficiently cause `x`'s own esse.

Disjunction elimination then gives an existing external efficient cause.
The Lean theorem is
`TruthCore.Results.Aquinas.SummaTheologiae.EssenceEsseExternalCause.distinctEsseExternalFromExhaustion`.

The theorem is a **conditional transcription**, explicitly not the
independent metaphysical proof of either premise. In particular, no
`A ∨ B → B` conclusion is being passed off as proof that the disjunction
itself must hold.

## Three actual-witness controls

`premiseOmissionsAndControl` constructs typed finite models with a subject
that really satisfies `InAct x esse` and `esseOf x ≠ essenceOf x`; every
recorded efficient cause of esse has existing relata.

| Case | Causal exhaustiveness | No efficient self-cause | Actual external efficient cause | Interpretation |
| --- | --- | --- | --- | --- |
| Brute distinct esse | **False** | True | **Absent** | No cause-of-esse relation at all; an abstract brute-fact rival |
| Essential efficient self-cause | True | **False** | **Absent** | The subject's essential principles are said to suffice alone as an efficient cause of its own esse |
| External-cause control | True | True | **Present** | A distinct actual bearer efficiently causes the subject's esse |

The omissions show that the two premises contribute independently to the
derivation and the positive case prevents merely vacuous success. They do
**not** prove brute being or efficient self-causation is metaphysically
possible. Rejecting the omitted premise requires a positive rival theory,
not just formal satisfiability.

## Alternative explanatory accounts

| Theory proposal | What it needs to explain | Relationship to the first proof |
| --- | --- | --- |
| Thomistic essence/esse and act/potency | Why a distinct act of being is dependent and cannot be efficiently originated solely by the thing's own essence | Accepts both *causal* premises; stronger act/potency and participation arguments are separate |
| Leibnizian sufficient reason | Why the existence fact is true, and why the contingent order exists, with necessary explanations permitted | May demand an ultimate sufficient reason without identifying *every* reason with another efficient cause of esse |
| Brute contingent existence | Why some particular existent exists, if no further reason is accepted | Rejects the causal-exhaustiveness premise; its explanatory answer is explicitly “unexplained” |
| Intrinsic **noncausal** grounding | What of a subject's nature or essence could account for the existence fact without efficiently causing itself | Does not contradict the *no efficient self-cause* premise; challenges the causal dichotomy if the subject's essence and esse remain distinct |
| Global or non-well-founded grounding | What explains the whole configuration or existence facts as a system | Cannot be equated with a source agent's `CausesIn y x esse` without a defended bridge |

This highlights a potential **equivocation**: ruling out a thing's
efficient **self-causation** does not yet rule out a noncausal **intrinsic
reason** for its existence. Also, knowing that a thing is actual or
exists at every accessible world does not give a cause or a reason by
definition. The q.3 inference is not a proof of modal necessity, divine
simplicity, numerical uniqueness of God, or the unrestricted PSR.

## Frontier / premise accounting

- **Reused:** pinned q.3 a.4 and q.104 a.1 witnesses, Leibniz PSR witness,
  existing `InAct`, `esse`, `CausesIn`, `essenceOf`/`esseOf` vocabulary and
  the existence/power disambiguation of #319.
- **New source readings:** two independently addressable premises from
  the q.3 a.4 first proof, added alongside its *existing* source claim
  for the conclusion. Neither premise's truth is certified by Lean.
- **Proved:** conditional consequence and three finite interpretation
  witnesses (one positive, two omissions), subject to independent
  Comparator verification.
- **Root-path premises discharged:** **zero**. The philosophical question
  has been relocated to defensible open propositions and competing
  accounts, not solved in favor of a particular metaphysics.

**Next valuable test:** make the rival "noncausal intrinsic explanation"
fully typed as an explanation of an *existence fact*, then ask which
additional source-defended principle excludes it when esse and essence
differ. In parallel, do not treat the existence-PSR in #312 as an
efficient-causation axiom. Any eventual route to simplicity or uniqueness
must still reuse the independently open #319/#320 bridges.

## Review corrections (2026-10-26)

The pinned Latin's `tantum` and `sufficit` restrict the internal alternative
to sufficient efficient causation by essential principles **alone**. The
earlier broad wording was rejected because negating it would also exclude
contributory causation, which this sentence does not establish. The revised
claim/definition and `essentialPrinciplesAloneSufficeForEsse` field preserve
that restriction. The Challenge theorem signatures remain unchanged.

The omission proposition now explicitly records absence of an external cause
for the designated subject, its internal predicate, and an empty efficient
cause relation in the brute control; the positive control explicitly has
an external cause for that subject. The initial universal negations alone
did not certify these properties. Explicit constructive proof terms replace
`simp`, whose initial proof unexpectedly required `propext`.

The conditional result declares `transcription: assembly`, so frontier
accounting keeps its conclusion open while either causal premise is open.
No philosophical premise is discharged by these corrections.
