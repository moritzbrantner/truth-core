# Third Man and likeness: what actually produces each regress

Issue #258 extends the shared `Forms.Vocabulary` from #257. It introduces no
second ontology of Forms. Both proofs construct arbitrarily long finite lists of
numerically distinct Forms of **one admitted quality**. They neither assume an
infinity premise nor infer that an infinite multiplicity is philosophically
impossible. Numerical multiplication contradicts `UniqueForms`; by itself it
refutes neither every Platonism nor Catholicism.

## Source evidence and interpretation

The new manifests use the existing immutable Perseus snapshots at
`a065c359aab33c33bd17ddc2cac7d27fdc9cd870`. Parmenides has blob
`c4020e0582e37ce886c935a6cd7f4a6202d189bd`; Metaphysics has blob
`4c03d2664d8acf43e49ce1b060d3e99f0e07c548`. The complete materialized Greek
pages `PLATO-PARM-131`, `PLATO-PARM-132`, `PLATO-PARM-133` and chapter
`ARIST-MET-I-9` were read. Page 131 preserves the preceding participation
problem; page 133 includes context after the likeness argument. The manifests
can be reused by #259 without creating competing bindings for page 133.

| Primary range | What the bounded claim records |
| --- | --- |
| Parmenides 132a | Looking over things that seem great motivates one common Greatness. |
| 132a–b | Greatness itself is considered with the other great things, and another common greatness is conceded. The literal same-predication reading is tested; universal self-predication is not attributed to Plato. |
| 132b | Another Form besides the earlier Form and participants, another over all these again, and the stated unlimited multitude. This assertion is kept distinct from the independently checked reconstruction. |
| 132b–c | The thought-in-souls response and questions about its object/participants. No full theory of intentionality or refutation of conceptualism is claimed. |
| 132d | Socrates proposes paradigms/copies and participation as being likened. |
| 132d–e | Reverse resemblance in the relevant respect and a common Form for things alike. |
| 133a | The renewed multiplication motivates seeking participation through something other than likeness. This reply remains visible beside the objection. |
| Metaphysics I.9, 990b15–17 | Aristotle names the Third Man among consequences of arguments for Forms; this is naming context, not a detailed proof of either Parmenides argument. |
| 991a2–8 | The same-character versus mere-homonymy dilemma pressures different-sense predication. It does not establish that ordinary exemplification and essential characterization must coincide. |
| 991a20–31 | Paradigm/participation language faces an explanatory challenge; resemblance need not be copying, and the same thing may be model and image. |

The source statements are prose readings of these sentences. Their `supports`
edges motivate independent schematic premises without making a bounded source
claim assert a universal quantifier. In particular, universal domain iteration,
participant-wide nonidentity and formation for every eligible finite plurality
remain explicit open reconstructions. Greek evidence has no translation flag.
Source integrity does not certify these interpretive choices.

## The two checked constructions

`THIRD-MAN-REGRESS` binds `Regress.regress` to six independently named premises:

1. `PropertyInstances`: two distinct ordinary F-particulars, one admitted quality.
2. `InitialScope`: their pair is eligible.
3. `Formation`: an eligible genuine plurality whose members ordinarily exemplify
   F has a common Form, with all members participating in it.
4. Existing `UniformSelfPredication`: each Form ordinarily exemplifies its quality.
5. `ParticipantNonidentity`: for every admitted q, Form f of q and **every**
   participating entity x, `f ≠ x`, including when x is another Form.
6. `Iteration`: adjoining a Form of q preserves the eligibility of the list.

Given an old list of Forms plus the original two particulars, formation supplies
a new Form. Nonidentity makes it different from each old Form. Self-predication
makes it an ordinary F-bearer, and iteration makes the enlarged list eligible.
Induction yields a pairwise-distinct Form list of each finite length. No premise
already has unboundedness as its consequent. A list presents a plurality; repeated
entries alone cannot satisfy `Plural`.

The new inequality is deliberately stronger than #257's `Nonidentity`, which
only quantifies over participating **particulars**. Neither inequality is the
predicate `Independent`, and neither numerical distinction nor ontological
independence establishes the additional domain closure.

`LIKENESS-REGRESS` binds `LikenessRegress.likenessRegress` to a distinct six-premise
argument: `LikenessSeed`, `LikenessFormation`, `LikenessSymmetry`,
`ParticipationLikeness`, `ParticipantNonidentity` and `Iteration`. The designated
quality is likeness, held fixed through the construction. The seed can be a copy
and paradigm rather than two ordinary particulars. A common Form receives all
old members as participants. The participation-to-resemblance bridge and symmetry
make it mutually resemble all of them, while nonidentity makes it new. Repeat.
This proof uses **no ordinary self-predication or ordinary F-homogeneity**.
It does not infer resemblance from modelhood or directed imitation alone.

`THIRD-MAN-NOT-UNIQUE` composes with either result: take its length-two list,
whose distinct members have the same admitted quality, to derive
`NotUniqueForms`. Thus adding `UniqueForms` to either complete premise set is
inconsistent. Omitting uniqueness leaves numerical multiplication, not a
contradiction. The result does not introduce uniqueness as a hidden premise.

## Countermodels and replies

`THIRD-MAN-SENSITIVITY` binds `Sensitivity.sensitivityModels` to six concrete
models on the common three-element type `{form, a, b}`. In all models only `form`
is a Form, so unbounded distinct Forms are false. The proof explicitly eliminates
the supposed length-two distinct Form list. Each case proves both the retained
commitments and the negation of the omitted principle; these are countermodels,
not failures to find a proof.

| Named premises / variant | Formal status relative to those premises | Witness or proof |
| --- | --- | --- |
| All six Third Man premises | **derivable**: unbounded numerical Forms | Finite-list induction in `Regress.Solution` |
| All six likeness premises | **derivable**: unbounded numerical Forms | Separate mutual-resemblance induction |
| Either full set plus numerical uniqueness | **inconsistent** | Derived unboundedness and `NotUnique.notUnique` |
| Third Man without formation | **not derivable** | `small`, eligibility unrestricted: the other five premises hold, but a plurality containing the Form cannot receive a fresh common Form. |
| Third Man without ordinary self-predication | **not derivable** | `nonSelf`: only a and b ordinarily exemplify F. The Form has `Essentially` F, all eligible homogeneous pluralities participate in it, and domain iteration/nonidentity hold. |
| Third Man without participant-wide nonidentity | **not derivable** | `selfParticipating`: the single Form also participates in itself; every eligible homogeneous plurality can use that same Form. |
| Third Man without domain iteration | **not derivable** | `small`, eligibility restricted to lists of ordinary particulars. Ordinary self-predication, the other five premises and a unique independent explanatory/exemplar Form coexist. |
| Likeness without symmetry | **not derivable** in the directed interpretation | `directed`: a and b mutually relate and each points to the Form, while the Form does not point back. The other five premises hold. This diagnoses replacing directed likeness-to-model with symmetric resemblance; it is not a counterexample to symmetry of ordinary resemblance. |
| Likeness without participation implying resemblance | **not derivable** | `nonResemblance`: symmetric resemblance relates a and b; their directed participation goes to the Form without resemblance to it. The other five premises hold. |

Asymmetrical participation is present in `small`, `nonSelf`, `directed` and
`nonResemblance`: a or b participates in the Form and the Form never participates
back. Asymmetry **alone** would not block the likeness proof if participation
still entailed symmetric resemblance. The strongest non-resemblance reply keeps
symmetric generic resemblance and rejects that bridge, as 133a invites. Directed
imitation remains available without equating it to generic resemblance.

For humanity, `Exemplifies form human` would say the Form is human in the same
ordinary predicative sense as Socrates. `Essentially form human` instead records
its essential characterization, with **no conversion** into ordinary
exemplification. The `nonSelf` countermodel demonstrates this distinction for
its sole admitted quality; it does not assume that the historically unsettled
human Form is admitted, or that essential characterization is vacuous ordinary
predication at another name. Aristotle's homonymy objection remains a pressure
on the philosophical adequacy of the reply, not a proved conversion between the
predicates.

The scoped reply is especially strong: it can retain self-predication, uniqueness,
ontological independence, explanatory participation and directed exemplar
participation while formation applies only to ordinary bearers. This is why the
foundation's scoped consistency result was not already a regress. The new models
reuse its relational vocabulary rather than introducing per-reading entities.
An interpretation supplies extensions for explanation/independence; it does not
prove those extensions explain actual property possession.

**Still open:** which reconstruction is historically best; whether a nonordinary
self-characterization or scoped formation supplies an adequate explanatory account;
whether an unbounded multiplicity is objectionable without uniqueness; and a full
semantics/proof for the thought response. No acceptance claim here closes a
Catholic-case frontier node or adjudicates whole/part or knowability (#259).

## Reproduction and self-review

The four result records each point to a frozen Challenge, separate Solution,
argument, inference and Comparator config. All permitted-axiom lists are empty;
Lean reports no axioms for all four result theorems. Direct inductive list
membership is used because some extensional convenience lemmas import axioms.
The shared conventions resolved to sourceRevision
`c104800c7aaeaea12d56f9093e71bdef6a2ce6fa`; no policy text is vendored.

Run the repository's source checks, `lake build`, `corpus.py check`,
`corpus.py bind-check`, and `scripts/verify-result.sh` for each of
`THIRD-MAN-REGRESS`, `LIKENESS-REGRESS`, `THIRD-MAN-SENSITIVITY` and
`THIRD-MAN-NOT-UNIQUE`. The self-sweep checks the bounded source attributions,
quantifiers, ordinary/essential predication, particulars-only/participant-wide
nonidentity, directed/symmetric likeness, formation scope, and every definition
and disambiguation link. These argument branches have no path to the Catholicism
root; their claims do not inherit a global verdict from the result names.
