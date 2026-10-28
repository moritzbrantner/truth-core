# Theseus: replacement, reassembly and numerical identity

The target is Q-IDENTITY in #325, not composition, life, grounding or modal
necessity. The existing `Mereology.Vitalism` profile (`STMT-MEREO-SOUL-UNITY-INDEPENDENCE`)
explicitly treats operational continuity as distinct from numerical identity.
Its life/soul predicates would add irrelevant assumptions here. Its checked
independence theorem is not restated as a premise. No existing Theseus module
or reassembly result was found.

## Read source and rejected attribution

Pinned primary translation: `PLUTARCH-THESEUS-23-EN`, Plutarch, *Theseus* 23,
especially 23.1, Bernadotte Perrin (1914). Materialization was run and the
verified chapter read in full; chapters 22 and 24 were also read in the same
pinned TEI for immediate context. Immutable witness:
<https://raw.githubusercontent.com/PerseusDL/canonical-greekLit/a6eb0cc3e6f6e382934a2c8b33577d2fb4371e00/data/tlg0007/tlg001/tlg0007.tlg001.perseus-eng3.xml>.

23.1 reports maintenance by replacing old timbers, and conflicting philosophical
identity judgments. It does not settle a criterion of persistence. Reassembly
of discarded components, final coexistence, and the formal identity bridges
below are **analytical extensions**, not claims about what Plutarch asserted.
23.2–3 moves to festival practices; 22 concerns the return, Aegeus and ritual
origins, and 24 political unification. Nothing in that immediate context adds
an identity verdict. No attributed corpus claim was invented to log this reading.

## Explicit analytical profile and result

There are four occurrences: original, halfway replacement, continued final ship,
and reassembled original components. Occurrences are not themselves the objects.
A function to a bearer type assigns which object occurs at each occurrence.
Ordinary equality of bearers represents numerical identity, independently of
component facts. Two slots track their own old/new component identities:

| Occurrence | First slot | Second slot |
| --- | --- | --- |
| original | old A | old B |
| intermediate | new A | old B |
| continued | new A | new B |
| reassembled | old A | old B |

The profile fixes two sequential one-part replacements, then compares two final
occurrences. It has no spatial geometry, mechanics or empirical sufficiency
claim. Final bearer distinction is assumed separately, never deduced from
stage names. One can dispute the real applicability of that premise.

- **G:** numerical identity persists across each replacement step.
- **M:** equality of these exact component inventories suffices for bearer
  identity. This is stronger than equal shape and is not essential parthood
  (identity implies same parts, the opposite direction).
- **D:** continued and reassembled final bearers are distinct.

The proof computes that M in this fixture is equivalent to original/reassembled
bearer identity. G gives original/continued bearer identity; symmetry/transitivity
then contradict D. Thus G, M and D form an incompatible bundle. For decidable
bearer equality the proof supplies the exhaustive fork ¬G ∨ ¬M ∨ ¬D, without
an exclusivity claim. The incompatibility itself requires no decidability.
A separate induction proves that identity at each adjacent step entails identity
of the endpoints for **any finite number** of steps; merely increasing the
number of replacements does not avoid this consequence.

Each pair has a concrete witness using the **same** inventories/history:

| Model | Original | Intermediate | Continued | Reassembled | Retains | Rejects |
| --- | --- | --- | --- | --- | --- | --- |
| history | false | false | false | true | G, D | M |
| material | false | true | true | false | M, D | G |
| collapsed | false | false | false | false | G, M | D |

Bool values are bearer labels, not component labels. These witnesses show
minimality of the conflicting principle set **in this explicit signature**;
they do not establish possible ships. The collapsed control is especially not
advertised as a physically adequate theory of spatially separated ships.
Constitution or stage/counterpart views require their own bridge from their
relations to numerical identity. The theorem neither refutes those views nor
silently identifies their relations with equality.

## Actual premise comparison and limits

Intended and actual root-path delta: **no change**. The result has no ordinary
premises: it proves a universally conditional incompatibility, a decidable
coverage theorem, three closed finite interpretations and a finite-chain lemma.
Application to actual ships retains open G/M/D and the adequacy of the bearer
and component profile. No one member is preferentially rejected. No premise
about soul, substantial unity, causal dependence, grounding, necessary existence
or Catholicism is discharged; no root argument is connected by an implicit edge.

## Verification evidence

The frozen Challenge precedes Solution work. Focused development used the shared
warm session `causal-harvest`, explicit workspace
`/home/brantner/privat/truth-core-sprint-proof`, under `/tmp/truth-core-lean.lock`.
Successful diagnostic v5 on `f2db33e8273b214f158d63e2e3a17094ba181735`, path
`Scratch/TheseusIdentity.lean`, content SHA256
`3e0e0e0312ab086859bb2a1eb7b7c8ff37e9699a3f779ee95a704478c5d53244`,
concatenated the exact vocabulary and Solution bodies (replacing only the local
import). No errors; `#print axioms` reported no axioms. Initial wildcard match
compilation introduced `propext`; exhaustive constructor definitions removed it.
No full local build was repeated. Final PR CI must certify the delivered revision
through build, binding, Comparator and NanoDa. Reproduce focused canonical proof
verification with `scripts/verify-result.sh THESEUS-IDENTITY-BOUNDARY` after build.
