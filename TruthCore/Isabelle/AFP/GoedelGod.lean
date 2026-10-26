import TruthCore.Modal.Kripke

/-!
Dana Scott's variant of Gödel's ontological argument, as formalized by
Christoph Benzmüller and Bruno Woltzenlogel Paleo in the Isabelle Archive of
Formal Proofs entry *GoedelGod* (theory `GoedelGod.thy`, pinned as the web
snapshot `AFP-GOEDELGOD-THY` of source `AFP-GOEDELGOD`).

The AFP theory is the formalization reference. It is a secondary witness for
Scott's notes, which are not pinned. Each claim attributes what the AFP
theory states. No claim, and no result built on these definitions, says what
Gödel or Scott intended.

## The embedding (quantified modal logic KB in Lean)

The AFP theory embeds quantified modal logic in classical higher-order logic.
This module mirrors that embedding with the least machinery that keeps it
faithful:

* **Worlds and accessibility.** The AFP type `i` of possible worlds and its
  accessibility relation `r` are a `TruthCore.Modal.Frame World`. No frame
  condition is built in. Symmetry (the AFP axiom `sym`, modal logic B) is the
  premise `TruthCore.Modal.Symmetric`, stated in each result that uses it.
  Reflexivity (T) is never assumed.
* **Individuals.** The AFP type `μ` is the type parameter `Ind`.
* **Modal propositions.** The AFP type `σ = i ⇒ bool` is `MProp World`, a
  predicate on worlds. The AFP lifted connectives `m¬`, `m∧`, `m→`, `∀`, `∃`
  are evaluated pointwise, so `(m¬ φ) w` is written `¬ φ w` and so on. Only
  `□`, `◇`, validity `[_]` and Leibniz equality `mL=` get names (`Box`,
  `Dia`, `MValid`, `LeibnizEqual`).
* **Properties.** A property is `Ind → MProp World`, the AFP type
  `μ ⇒ σ`: an intensional property, whose extension may differ from world to
  world.
* **Quantifier domains.** The AFP quantifiers `∀` and `∃` range over the whole
  type at every world. So do the Lean quantifiers here. This is the
  possibilist (constant-domain) reading: the same individuals are quantified
  over in every world, and there is no separate existence predicate.
  Property quantifiers range over every function `Ind → MProp World`, as in
  HOL, so the full comprehension the AFP proofs use is available.
* **Positivity.** The AFP constant `P` is the parameter
  `P : Positivity World Ind`. It is constrained only by the axioms below.
* **Classical logic.** HOL is classical. Lean is not, unless an axiom is
  used. Results built on this module take excluded middle as the explicit
  premise `TruthCore.Logic.ExcludedMiddle` (statement `STMT-EXCLUDED-MIDDLE`)
  instead of using `Classical.em`, and Comparator checks them with
  `permitted_axioms: []`.

The definitions `GodLike`, `Essence` and `NecessaryExistence` are the AFP
definitions `G`, `ess` and `NE`. They are definitions, not premises: unfolding
them is how the results are proved.
-/

namespace TruthCore.Isabelle.AFP.GoedelGod

open TruthCore.Modal

universe u v

/-- AFP `σ`: a proposition of the embedded modal logic, true or false at each
world. -/
abbrev MProp (World : Type u) := World → Prop

/-- AFP `μ ⇒ σ`: a property of individuals, whose extension may vary from
world to world. -/
abbrev Property (World : Type u) (Ind : Type v) := Ind → MProp World

/-- AFP `(μ ⇒ σ) ⇒ σ`: the type of the constant `P`, "positive", which says at
each world which properties are positive there. -/
abbrev Positivity (World : Type u) (Ind : Type v) := Property World Ind → MProp World

variable {World : Type u} {Ind : Type v}

/-- AFP `□ φ ≡ (λw. ∀v. w r v ⟶ φ v)`. -/
def Box (F : Frame World) (φ : MProp World) : MProp World :=
  fun w => ∀ v, F.access w v → φ v

/-- AFP `◇ φ ≡ (λw. ∃v. w r v ∧ φ v)`. -/
def Dia (F : Frame World) (φ : MProp World) : MProp World :=
  fun w => ∃ v, F.access w v ∧ φ v

/-- AFP `[p] ≡ ∀w. p w`: validity, truth at every world. -/
def MValid (φ : MProp World) : Prop :=
  ∀ w, φ w

/-- AFP definition `G`: `G = (λx. ∀(λΦ. P Φ m→ Φ x))`. An individual is
God-like at a world when it has, there, every property that is positive
there. -/
def GodLike (P : Positivity World Ind) : Property World Ind :=
  fun x w => ∀ Φ : Property World Ind, P Φ w → Φ x w

/-- AFP definition `ess`: `Φ ess x = Φ x m∧ ∀(λΨ. Ψ x m→ □ (∀(λy. Φ y m→ Ψ y)))`.
`Φ` is an essence of `x` at a world when `x` has `Φ` there and every property
`x` has there is necessarily had by everything that has `Φ`. -/
def Essence (F : Frame World) (Φ : Property World Ind) (x : Ind) : MProp World :=
  fun w => Φ x w ∧
    ∀ Ψ : Property World Ind, Ψ x w → Box F (fun v => ∀ y, Φ y v → Ψ y v) w

/-- AFP definition `NE`: `NE = (λx. ∀(λΦ. Φ ess x m→ □ (∃ Φ)))`. An
individual exists necessarily at a world when each of its essences there is
necessarily exemplified. -/
def NecessaryExistence (F : Frame World) : Property World Ind :=
  fun x w => ∀ Φ : Property World Ind, Essence F Φ x w → Box F (fun v => ∃ y, Φ y v) w

/-! ## Axioms (premises) -/

/-- AFP axiom `A1a`: `[∀(λΦ. P (λx. m¬ (Φ x)) m→ m¬ (P Φ))]`. If the negation
of a property is positive, the property is not positive. -/
def NegationPositiveExcludesPositive (P : Positivity World Ind) : Prop :=
  ∀ w (Φ : Property World Ind), P (fun x v => ¬ Φ x v) w → ¬ P Φ w

/-- AFP axiom `A1b`: `[∀(λΦ. m¬ (P Φ) m→ P (λx. m¬ (Φ x)))]`. If a property is
not positive, its negation is positive. -/
def NonPositiveHasPositiveNegation (P : Positivity World Ind) : Prop :=
  ∀ w (Φ : Property World Ind), ¬ P Φ w → P (fun x v => ¬ Φ x v) w

/-- AFP axiom `A2`: `[∀(λΦ. ∀(λΨ. (P Φ m∧ □ (∀(λx. Φ x m→ Ψ x))) m→ P Ψ))]`.
A property necessarily implied by a positive property is positive. -/
def PositiveClosedUnderNecessaryImplication (F : Frame World)
    (P : Positivity World Ind) : Prop :=
  ∀ w (Φ Ψ : Property World Ind),
    P Φ w → Box F (fun v => ∀ x, Φ x v → Ψ x v) w → P Ψ w

/-- AFP axiom `A3`: `[P G]`. Being God-like is positive. -/
def GodLikePositive (P : Positivity World Ind) : Prop :=
  MValid (P (GodLike P))

/-- AFP axiom `A4`: `[∀(λΦ. P Φ m→ □ (P Φ))]`. Positive properties are
necessarily positive. -/
def PositiveNecessarilyPositive (F : Frame World) (P : Positivity World Ind) : Prop :=
  ∀ w (Φ : Property World Ind), P Φ w → Box F (P Φ) w

/-- AFP axiom `A5`: `[P NE]`. Necessary existence is positive. -/
def NecessaryExistencePositive (F : Frame World) (P : Positivity World Ind) : Prop :=
  MValid (P (NecessaryExistence F))

/-! ## Derived propositions (theorems of the AFP theory) -/

/-- AFP theorem `T1`: `[∀(λΦ. P Φ m→ ◇ (∃ Φ))]`. Positive properties are
possibly exemplified. -/
def PositivePossiblyExemplified (F : Frame World) (P : Positivity World Ind) : Prop :=
  ∀ w (Φ : Property World Ind), P Φ w → Dia F (fun v => ∃ x, Φ x v) w

/-- AFP corollary `C`: `[◇ (∃ G)]`. Possibly, a God-like being exists. -/
def GodLikePossiblyExists (F : Frame World) (P : Positivity World Ind) : Prop :=
  MValid (Dia F (fun v => ∃ x, GodLike P x v))

/-- AFP theorem `T2`: `[∀(λx. G x m→ G ess x)]`. Being God-like is an essence
of every God-like being. -/
def GodLikeIsEssence (F : Frame World) (P : Positivity World Ind) : Prop :=
  ∀ w (x : Ind), GodLike P x w → Essence F (GodLike P) x w

/-- AFP theorem `T3`: `[□ (∃ G)]`. Necessarily, a God-like being exists: at
every world, every accessible world has a God-like individual. -/
def GodLikeNecessarilyExists (F : Frame World) (P : Positivity World Ind) : Prop :=
  MValid (Box F (fun v => ∃ x, GodLike P x v))

/-- AFP corollary `C2`: `[∃ G]`. A God-like being exists, at every world. The
AFP theory remarks that this follows without reflexivity. -/
def GodLikeActuallyExists (P : Positivity World Ind) : Prop :=
  MValid (fun w => ∃ x, GodLike P x w)

/-- AFP theorem `Flawlessness`:
`[∀(λΦ. ∀(λx. (G x m→ (m¬ (P Φ) m→ m¬ (Φ x)))))]`. A God-like being has no
property that is not positive. -/
def GodLikeFlawless (P : Positivity World Ind) : Prop :=
  ∀ w (Φ : Property World Ind) (x : Ind), GodLike P x w → ¬ P Φ w → ¬ Φ x w

/-- AFP abbreviation `mL=`: `x mL= y ≡ ∀(λφ. (φ x m→ φ y))`, Leibniz equality
at a world. At `w`, every property `x` has there, `y` has there. With the full
property domain of this embedding, this is equivalent to Lean equality of
individuals: instantiate the property with `fun z _ => x = z`. -/
def LeibnizEqual (x y : Ind) : MProp World :=
  fun w => ∀ Φ : Property World Ind, Φ x w → Φ y w

/-- Full property quantification makes AFP Leibniz equality at any world
equivalent to identity. No modal or positivity premise is needed. -/
theorem leibnizEqualIffEq (x y : Ind) (w : World) :
    LeibnizEqual x y w ↔ x = y := by
  constructor
  · intro h
    exact h (fun z _ => x = z) rfl
  · intro h
    cases h
    exact fun _ hΦ => hΦ

/-- AFP theorem `Monotheism`: `[∀(λx.∀(λy. (G x m→ (G y m→ (x mL= y)))))]`.
Any two God-like beings at a world are Leibniz-equal there, hence identical
in this embedding: at most one God-like individual per world. This does not
establish existence; together with `C2`, it gives exactly one per world. -/
def GodLikeUnique (P : Positivity World Ind) : Prop :=
  ∀ w (x y : Ind), GodLike P x w → GodLike P y w → LeibnizEqual x y w

/-- AFP lemma `MC`: `[∀(λΦ.(Φ m→ (□ Φ)))]`, modal collapse. Whatever is true
at a world is necessary there. The AFP theory states it and leaves it
unproved in Isabelle (`oops`), reporting that the prover Satallax confirms
it. -/
def ModalCollapse (F : Frame World) : Prop :=
  ∀ w (φ : MProp World), φ w → Box F φ w

/-- The empty property is an essence of nothing: at no world is `λ_ _. False`
an essence of any individual. Not a statement of the AFP theory. It follows
from the conjunct `Φ x` of the definition `ess`, and it is the point where
Scott's essence differs from Gödel's 1970 essence
(`TruthCore.Isabelle.AFP.NotesOnGoedel.GoedelVariantHOML1.EmptyPropertyIsEssence`). -/
def EmptyPropertyNotEssence (F : Frame World) (Ind : Type v) : Prop :=
  ∀ w (x : Ind), ¬ Essence F (fun _ _ => False) x w

/-- A finite independence test for Scott's axiom `A5`. There can be two
universally accessible worlds and one individual satisfying `A1a`, `A1b`,
`A2`, `A3`, and `A4`, while necessary existence is not positive and `T3`
fails. The possibility corollary `C` is nevertheless true. This is a new
logical countermodel concerning the AFP formalization, not a historical
claim about Scott's philosophical justification for `A5`. -/
def NecessaryExistencePositivityIndependent : Prop :=
  ∃ (F : Frame Bool) (P : Positivity Bool Unit),
    Reflexive F ∧
    Symmetric F ∧
    Transitive F ∧
    NegationPositiveExcludesPositive P ∧
    NonPositiveHasPositiveNegation P ∧
    PositiveClosedUnderNecessaryImplication F P ∧
    GodLikePositive P ∧
    PositiveNecessarilyPositive F P ∧
    GodLikePossiblyExists F P ∧
    ¬ NecessaryExistencePositive F P ∧
    ¬ GodLikeNecessarilyExists F P

/-- In the AFP embedding with quantification over **every** intensional
property, Scott's `NE x` is equivalent to the *world-level* condition that
every accessible world is identical to the current world. This uses the
property `fun y v => y = x ∧ v = w`, which is an essence of `x` at `w` but
cannot be exemplified at any distinct world. Conversely, if there are no
distinct accessible worlds, any essence is exemplified by `x` at each
accessible world. This characterizes the AFP definition, not metaphysical
necessary existence under every possible restriction of property domains. -/
def NecessaryExistenceWorldIsolation (World : Type u) (Ind : Type v) : Prop :=
  ∀ (F : Frame World) (x : Ind) (w : World),
    NecessaryExistence F x w ↔ ∀ next, F.access w next → next = w

end TruthCore.Isabelle.AFP.GoedelGod
