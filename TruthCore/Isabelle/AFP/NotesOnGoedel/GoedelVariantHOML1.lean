import TruthCore.Isabelle.AFP.GoedelGod

/-!
Kurt Gödel's 1970 variant of the ontological argument, as formalized by
Christoph Benzmüller and Dana Scott in the Isabelle Archive of Formal Proofs
entry *Notes on Gödel's and Scott's Variants of the Ontological Argument*
(theory `GoedelVariantHOML1.thy`, "Gödel's ontological argument -- 1970
manuscript", pinned as the web snapshot `AFP-NOTES-GOEDEL-HOML1-THY`, on the
embedding `HOMLinHOL.thy`, pinned as `AFP-NOTES-GOEDEL-HOMLINHOL-THY`, both of
source `AFP-NOTES-GOEDEL-ONTOLOGICAL`).

The AFP theory is the formalization reference. It is a secondary witness for
Gödel's 1970 manuscript, which is not pinned. Each claim attributes what the
AFP theory states. No claim, and no result built on these definitions, says
what Gödel intended or how his manuscript developed.

This variant is kept separate from Scott's (`TruthCore.Isabelle.AFP.GoedelGod`,
#134). Declarations are shared only where the formulas coincide:

* `MProp`, `Property`, `Positivity`, `Box`, `Dia`, `MValid`: the `HOMLinHOL`
  types `σ`, `τ`, the constant type of `P`, and the abbreviations `❙□`, `❙◇`,
  `⌊_⌋` have the same definitions as their `GoedelGod.thy` counterparts.
* `GodLike`: `G x ≡ ❙∀φ. P φ ❙⊃ φ x` is Scott's `G`, with the possibilist
  property quantifier. The positivity constant it is applied to is constrained
  by different axioms.
* `PositiveNecessarilyPositive`: `Ax2b`, `⌊P φ ❙⊃ ❙□ P φ⌋`, is Scott's `A4`.

Everything else is new, because it differs:

* **Essence.** `φ Ess. x ≡ ❙∀ψ. ψ x ❙⊃ (φ ❙⊃⇩N ψ)` lacks Scott's conjunct
  `Φ x`, and its inclusion `❙⊃⇩N` quantifies actualistically. So the empty
  property is an essence of everything (`EmptyPropertyIsEssence`), which Scott's
  definition excludes (`GoedelGod.EmptyPropertyNotEssence`).
* **Quantifiers over individuals.** `HOMLinHOL` has actualist quantifiers
  `❙∀⇧E`, `❙∃⇧E`, relative to the constant `existsAt` ("x exists at w"), here
  the parameter `ex : ExistsAt World Ind`. The theory uses them for every
  quantification over individuals. Property quantifiers stay possibilist and
  range over every function `Ind → MProp World` (full comprehension).
  Scott's theory has only possibilist quantifiers.
* **Necessary existence.** `E x ≡ ❙∀φ. φ Ess. x ❙⊃ ❙□(❙∃⇧Ex. φ x)` uses this
  essence and the actualist existential.
* **Axioms.** `Ax1` (conjunction), `Ax2a` (exclusive or), `Ax3` (`P E`) and
  `Ax4` (closure under actualist necessary inclusion) differ from Scott's
  `A1a`, `A1b`, `A2`, `A3`, `A5`. There is no axiom that `G` is positive.
* **Frame.** `HOMLinHOL` axiomatizes S5: `Rrefl`, `Rsymm`, `Rtrans`. No frame
  condition is built in here. A result that uses one states it as a premise;
  only symmetry (`TruthCore.Modal.Symmetric`, as for Scott) is used, and the
  inconsistency uses none.

## Comparison with Scott's variant (bounded queries)

* **Consistency.** Scott: the premises of T3 hold in a model with a world
  (`SCOTT-PREMISES-SATISFIABLE-WITH-WORLD`; the older
  `premisesJointlySatisfiable` of `SCOTT-GOD-LIKE-NECESSARILY-EXISTS` does not
  require a world in its type).
  Gödel 1970: `Ax2a`, `Ax3`, `Ax4` have no model with a world, on any frame
  (`GOEDEL-1970-INCONSISTENT`); without `Ax4` the other axioms and symmetry are
  satisfiable (`GOEDEL-1970-POSSIBLE-GOD-LIKE-NECESSARILY-EXISTS`,
  `premisesJointlySatisfiable`).
* **What accounts for it.** The essence definitions: the empty property is an
  essence of everything in 1970 (`GOEDEL-1970-EMPTY-PROPERTY-IS-ESSENCE`) and of
  nothing for Scott (`SCOTT-EMPTY-PROPERTY-NOT-ESSENCE`), together with `Ax4`.
* **Main existence.** Scott derives `□(∃ G)` (T3). The 1970 theory derives
  only `◇(∃⇧E G) → □(∃⇧E G)` (`Th3`) from satisfiable premises; the
  unconditional claim follows from the full axiom set only by explosion.
* **Modal collapse.** Scott: derived through T3 (`SCOTT-MODAL-COLLAPSE`).
  Gödel 1970: by explosion only (`GOEDEL-1970-MODAL-COLLAPSE`).

Lean is not classical unless an axiom is used. No result built on this
module needs excluded middle except the satisfiability model, which takes it
as a hypothesis, so Comparator checks them with `permitted_axioms: []`.
-/

namespace TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1

open TruthCore.Modal
open TruthCore.Isabelle.AFP.GoedelGod
  (MProp Property Positivity Box MValid GodLike)

universe u v

/-- `HOMLinHOL` constant `existsAt :: e ⇒ σ` (`x ❙@ w`): which individuals
exist at which world. The actualist quantifiers range over them. -/
abbrev ExistsAt (World : Type u) (Ind : Type v) := Ind → MProp World

variable {World : Type u} {Ind : Type v}

/-- `GoedelVariantHOML1` abbreviation `PropertyInclusion`:
`φ ❙⊃⇩N ψ ≡ ❙□(❙∀⇧Ey. φ y ❙⊃ ψ y)`. Necessarily, every existing individual
that has `φ` has `ψ`. -/
def PropertyInclusion (F : Frame World) (ex : ExistsAt World Ind)
    (φ ψ : Property World Ind) : MProp World :=
  Box F (fun v => ∀ y, ex y v → φ y v → ψ y v)

/-- `GoedelVariantHOML1` definition `Essence`:
`φ Ess. x ≡ ❙∀ψ. ψ x ❙⊃ (φ ❙⊃⇩N ψ)`. `φ` is necessarily included in every
property `x` has at that world. Unlike Scott's `ess`, `x` need not have
`φ`. -/
def Essence (F : Frame World) (ex : ExistsAt World Ind)
    (φ : Property World Ind) (x : Ind) : MProp World :=
  fun w => ∀ ψ : Property World Ind, ψ x w → PropertyInclusion F ex φ ψ w

/-- `GoedelVariantHOML1` definition `NecExist` (`E`):
`E x ≡ ❙∀φ. φ Ess. x ❙⊃ ❙□(❙∃⇧Ex. φ x)`. Each essence of `x` is necessarily
exemplified by an existing individual. -/
def NecessaryExistence (F : Frame World) (ex : ExistsAt World Ind) :
    Property World Ind :=
  fun x w => ∀ φ : Property World Ind, Essence F ex φ x w →
    Box F (fun v => ∃ y, ex y v ∧ φ y v) w

/-! ## Axioms (premises) -/

/-- `GoedelVariantHOML1` axiom `Ax1`: `⌊P φ ❙∧ P ψ ❙⊃ P (φ ❙. ψ)⌋`. The
conjunction of two positive properties is positive. -/
def PositiveClosedUnderConjunction (P : Positivity World Ind) : Prop :=
  ∀ w (φ ψ : Property World Ind), P φ w → P ψ w →
    P (fun x v => φ x v ∧ ψ x v) w

/-- `GoedelVariantHOML1` axiom `Ax2a`: `⌊P φ ❙∨⇧e P ❙~φ⌋`. Exactly one of a
property and its negation is positive. -/
def PositiveOrNegationPositiveExclusively (P : Positivity World Ind) : Prop :=
  ∀ w (φ : Property World Ind),
    (P φ w ∨ P (fun x v => ¬ φ x v) w) ∧ ¬ (P φ w ∧ P (fun x v => ¬ φ x v) w)

/-- `GoedelVariantHOML1` axiom `Ax3`: `⌊P E⌋`. Necessary existence, in the
1970 sense, is positive. -/
def NecessaryExistencePositive (F : Frame World) (ex : ExistsAt World Ind)
    (P : Positivity World Ind) : Prop :=
  MValid (P (NecessaryExistence F ex))

/-- `GoedelVariantHOML1` axiom `Ax4`: `⌊P φ ❙∧ (φ ❙⊃⇩N ψ) ❙⊃ P ψ⌋`. A property
necessarily implied by a positive property, among existing individuals, is
positive. -/
def PositiveClosedUnderNecessaryInclusion (F : Frame World)
    (ex : ExistsAt World Ind) (P : Positivity World Ind) : Prop :=
  ∀ w (φ ψ : Property World Ind), P φ w → PropertyInclusion F ex φ ψ w → P ψ w

/-! ## Derived propositions -/

/-- `GoedelVariantHOML1` lemma `EmptyEssL`: `⌊(λy.❙⊥) Ess. x⌋`. The empty
property is an essence of every individual at every world. -/
def EmptyPropertyIsEssence (F : Frame World) (ex : ExistsAt World Ind) : Prop :=
  ∀ w (x : Ind), Essence F ex (fun _ _ => False) x w

/-- Step 1 of the theory's proof of `Inconsistency`: `⌊❙¬(P (λx.❙⊥))⌋`. The
empty property is not positive. -/
def EmptyPropertyNotPositive (P : Positivity World Ind) : Prop :=
  ∀ w, ¬ P (fun _ _ => False) w

/-- No world is a dead end: no world fails to access every world. This is not
a statement of the theory. It is the step the Lean proof of `Inconsistency`
takes where the theory's step 5 (`P (λx.❙□❙⊥)` to `P (λx.❙⊥)`) is closed by
`smt`, so that the proof needs no frame condition. -/
def NoDeadEndWorld (F : Frame World) : Prop :=
  ∀ w, ¬ ∀ v, ¬ F.access w v

/-- `GoedelVariantHOML1` theorem `Inconsistency: False`, stated for a Kripke
model: the model has no world. Every axiom is a validity (truth at every
world), so a model without worlds satisfies all of them vacuously; that the
axioms admit only such models is what their inconsistency amounts to. -/
def NoWorld (World : Type u) : Prop :=
  World → False

/-- `GoedelVariantHOML1` theorem `Th1`: `⌊G x ❙⊃ G Ess. x⌋`. Being God-like is
an essence, in the 1970 sense, of every God-like individual. -/
def GodLikeIsEssence (F : Frame World) (ex : ExistsAt World Ind)
    (P : Positivity World Ind) : Prop :=
  ∀ w (x : Ind), GodLike P x w → Essence F ex (GodLike P) x w

/-- `GoedelVariantHOML1` theorem `Th2`: `⌊G x ❙⊃ ❙□(❙∃⇧Ey. G y)⌋`. Wherever an
individual is God-like, necessarily an existing God-like individual exists. -/
def GodLikeImpliesNecessarilyExists (F : Frame World) (ex : ExistsAt World Ind)
    (P : Positivity World Ind) : Prop :=
  ∀ w (x : Ind), GodLike P x w → Box F (fun v => ∃ y, ex y v ∧ GodLike P y v) w

/-- `GoedelVariantHOML1` theorem `Th3`: `⌊❙◇(❙∃⇧Ex. G x) ❙⊃ ❙□(❙∃⇧Ey. G y)⌋`.
If an existing God-like individual possibly exists, one necessarily exists.
This is the theory's existence theorem: it does not derive the antecedent. -/
def PossibleGodLikeNecessarilyExists (F : Frame World) (ex : ExistsAt World Ind)
    (P : Positivity World Ind) : Prop :=
  MValid (fun w =>
    TruthCore.Isabelle.AFP.GoedelGod.Dia F (fun v => ∃ x, ex x v ∧ GodLike P x v) w →
      Box F (fun v => ∃ y, ex y v ∧ GodLike P y v) w)

end TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1
