# Arrangement dynamics and the nihilist alternative (#326)

## Question and research boundary

Can an arrangement-only account reproduce a nonlinear collective response over
intervention histories without counting the response-description as an extra
material bearer? The bounded answer is yes for an explicit family; a closely
related intervention defeats that particular coarse reduction. Neither result
chooses the correct primitive ontology or establishes explanatory completeness.
This is a comparison of substantive commitments, not a refutation of material
composites, persons, substantial forms or Catholicism.

The precise certificate is `MEREO-ARRANGEMENT-DYNAMICS`, bound to
`TruthCore.Results.Mereology.ArrangementDynamics.controls`. It has no ordinary
philosophical premises: it quantifies over typed descriptions and constructs a
finite analyst model. All real-world applicability remains open. Mathlib's
`Function.FactorsThrough`, `Function.extend` and `Function.Semiconj` provide the
mathematics; this is not another generic static correctness-factorization result.

## Source evidence and interpretation

Primary context: Andrew Brenner, *Mereological Nihilism and Personal Ontology*,
author preprint, pp.5–8, Objections2–4, especially p.5 on arrangement predicates
and pp.7–8 on causal closure/exclusion. The passage
`BRENNER-PERSONAL-ONTOLOGY-ARRANGEMENT-CAUSAL-CONTEXT` was materialized and read,
including intervening law-parsimony context; nearby introduction establishes the
paper's dialectical purpose. PDF bytes matched two fetches. The public preprint
mirror is pinned by byte/text hashes; no redistribution permission or durable
archive fallback is asserted.

Brenner argues that arrangement predicates are available to both nihilists and
non-nihilists. His discussion compares physical and microphysical closure
arguments and explicitly acknowledges the reply that some composites might have
causal contributions not overdetermined by their proper parts. This is a
stronger rival than simply denying ordinary nouns. The mathematical certificate
below is our analyst construction, not Brenner's theorem, not an endorsement of
his parsimony argument, and not a formalization of every premise of exclusion.

The original 2015 *Theoretical Unification* lead was readable through a web PDF
viewer but local PhilArchive/PhilPapers byte fetches returned403. The
university-hosted *Mereology and Ideology* PDF also returned403. The author's
Google homepage selected text was stable but whole-page bytes changed between
fetches, so it was not pinned as a reproducible witness. These failed routes do
not establish that their philosophical positions are false. No bibliographic
record was manufactured to evade a readable, pinnable alternative.

## Exact dynamic constraint

For a microstate type `S`, macro-description type `M`, intervention type `I`,
observation `o : S → M` and primitive transitions `f : I → S → S`:

- A family `g : I → M → M` realizes the description exactly when every
  `f i` semiconjugates through `o` to `g i`.
- Such a family exists iff equal coarse inputs remain equal after every
  primitive intervention. This is Mathlib fiber constancy applied to `o ∘ f i`.
- Every realizing family preserves observation after every finite ordered list
  of interventions. The proof composes the one-step equations by induction.

There are no seriality, finiteness or nonemptiness hypotheses in this general
criterion, and it does not assert an actual microstate exists. The concrete
fixture is inhabited: individual bearers are the two Bool values, microstates
are pairs of bits, and macro-descriptions are single output bits. These are
separate types with separate roles. Mathematical pairs, functions and commands
are not additional members of the stipulated **material** bearer domain.

The identity-only material parthood relation has no proper parts. This is the
chosen nihilist semantic profile, not a derivation that nature has simples. It
does not imply that immaterial beings or all mathematical objects are absent.

## Finite response and intervention controls

The observation is `coupled && (left && right)`. Both individual bits contribute:
either bit alone gives false while both true give true in the coupled profile.
This is a nonlinear Boolean conjunction, not a claim of irreducible causal
agency or an additive physical-force law.

The admitted commands are exactly joint writes of two Boolean values and swaps
of their coordinates. The macro transition of a joint write returns the
corresponding conjunction; a swap leaves it unchanged. The general theorem
therefore certifies every finite history of those commands, not merely one
initial/final match. The same two individual bearers and same two intrinsic
bits can give different outputs when the arrangement parameter changes.

The enriched intervention flips just the left bit. The states `(false,false)`
and `(false,true)` have the same AND description but different successor
outputs under that flip. Consequently **no** macro transition on the single
AND bit realizes this extra intervention. The result is not that the primitive
account fails: retaining more micro-information restores a richer description.
It is that the proposed coarse state is insufficient for the enlarged family.

Thus matching the selected histories supplies neither unrestricted causal
closure nor the exclusion of genuine composite causes. A composite realist may
accept the same response equations while interpreting a substantial bearer or
constitution relation additionally. That rival must defend those commitments;
the nihilist must defend the sufficiency and real applicability of the
arrangement account. Their full ontologies are not compared by an aggregate
score or by counting mathematical helper lemmas.

## Shared-question answer map

The labels below are the shared questions of #325, not newly established
statement IDs or claims to have completed a theory.

| Question | Affirmative arrangement account in this slice | Strongest alternative / unresolved commitment |
| --- | --- | --- |
| Composition | Two simple material bearers interact under a specified state law; a joint response need not be an additional material individual in this interpretation. | Real composites might instantiate organizational or causal properties; the identity-only parthood assumption is not empirically defended here. |
| Unity | Coordinated response and stable macro histories have explicit equations. | Operational closure is not substantial unity; the real criterion for a substance remains open. |
| Life and soul | The model supplies an arrangement description rather than deleting coordinated behavior. | It is not a biological, conscious or personal-agent model. Neither souls nor their absence follow. A material nihilist need not reject an immaterial personal ontology. |
| Identity | The primitive identifiers remain fixed while their bits change. | Persistence of organisms/persons and replacement of constituents need further criteria. State equality is not bearer identity. |
| Grounding | Micro-to-macro history preservation has a precise conditional mathematical account. | Semiconjugacy is not metaphysical grounding, origination, or an actual conserving cause. |
| Explanation | The finite response pattern follows from the stated laws and commands; extra local intervention identifies omitted information. | The actual laws, privileged description, admissible interventions, and explanatory adequacy remain open rather than explained by the theorem. |
| Ultimate reality | No extra composite bearer is needed to describe this limited response model. | Why primitive bearers/laws exist, whether they are necessary, and whether an ultimate ground is simple or unique are unexplained here. |

## Reuse and downstream obligations

`TruthCore.Mereology.Vitalism` / `STMT-MEREO-SOUL-UNITY-INDEPENDENCE` already
separates operational life/turnover from substantial unity and soul predicates.
That fixed observational signature is not silently reused as numerical identity
or a dynamics of microstates: the present result adds specified intervention
transitions and finite-history composition. Theseus/reassembly and river
persistence results address different identity criteria; no change of identity
sense is used to count them as this model's continuation rule.

For #319, a demonstrated response difference is not the required
composition-to-actual-dependence bridge. Nor does a closed response model show
that an underived causal exercise makes its bearer independent in every respect.
The next decisive test is to defend a specific full intervention/explanandum
family for a real proposed case and see whether its primitive account satisfies
the exact closure condition. An adequate rival must replace the explanation it
rejects; a selected model is not a complete worldview by itself.

Intended and actual root-path premise change: none. All63 existing reaching-root
open premises are retained; the eight route costs are unchanged. There is no
root closure, no direct root edge, and no claim that the entire #326 investigation
is complete.
