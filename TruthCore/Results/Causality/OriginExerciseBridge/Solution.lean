module

public import TruthCore.Causality.OriginExerciseBridge
public import TruthCore.Causality.ExistentialSelfActualization
public import TruthCore.Results.Causality.ExistentialSelfActualization.Solution

@[expose] public section

namespace TruthCore.Results.Causality.OriginExerciseBridge

open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.OriginExerciseBridge
open TruthCore.Causality.ExistentialSelfActualization

/-- If every self-origin edge has an exercise of that very being producing its
own existence, an existing prohibition on productive self-actualization
excludes self-origin. This result has TWO explicit premises: the self-edge
bridge and the independently recorded NoSelfProduction statement. That latter
statement already has a certified route from four open priority premises.
Nothing defines CausesOrigin as irreflexive, and no premise concerns origin
edges between distinct beings (#1610). -/
theorem noSelfOriginFromSelfExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveSelfExercise F Occurs bearer produces)
    (hNoSelf : NoSelfProduction Occurs bearer produces) :
    NothingOriginatesItself F := by
  intro x hCausesOrigin
  obtain ⟨a, hOccurs, hBearerEq, hProduces⟩ := hOrigin x hCausesOrigin
  have hProducesBearer : produces a (bearer a) := by
    simpa [hBearerEq] using hProduces
  exact hNoSelf a hOccurs hProducesBearer

/-- The universal origin-to-exercise bridge entails its self-edge sibling:
instantiate the universal clause at the edge `CausesOrigin x x`. This backs
the `strengthens` registration (universal → self-edge). -/
theorem selfExerciseOfExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces) :
    OriginHasProductiveSelfExercise F Occurs bearer produces :=
  fun x hx => hOrigin x x hx

/-- Certified difference (#1598): the universal bridge is exactly its
self-edge sibling together with the clause for edges that are not self-edges.
Premise-free comparison of the two encodings. -/
theorem universalOverSelfExact : UniversalOverSelfExact := by
  intro Being Respect Exercise F Occurs bearer produces
  constructor
  · intro hOrigin
    exact ⟨fun x hx => hOrigin x x hx, fun c x hcx => Or.inr (hOrigin c x hcx)⟩
  · rintro ⟨hSelf, hOther⟩ c x hcx
    rcases hOther c x hcx with hEq | hExercise
    · subst hEq
      exact hSelf c hcx
    · exact hExercise

/-- Strictness: in the other-only setting the self-edge sibling holds and the
universal bridge fails. A formal interpretation only. -/
theorem otherOnlySeparates : OtherOnlySeparates := by
  refine ⟨trivial, ?_, ?_⟩
  · intro x hx
    cases x with
    | false => exact absurd hx.1 (by decide)
    | true => exact absurd hx.2 (by decide)
  · intro hOrigin
    obtain ⟨a, _⟩ := hOrigin true false ⟨rfl, rfl⟩
    exact nomatch a

/-- The earlier universal-bridge composition, kept as an unregistered check:
it factors through `selfExerciseOfExercise` and the self-edge result. -/
theorem noSelfOriginFromNoSelfProduction {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces)
    (hNoSelf : NoSelfProduction Occurs bearer produces) :
    NothingOriginatesItself F :=
  noSelfOriginFromSelfExercise F Occurs bearer produces
    (selfExerciseOfExercise F Occurs bearer produces hOrigin) hNoSelf

/-- Fully composed Lean witness: use the previously verified productive
self-actualization theorem to obtain NoSelfProduction from the four separately
open mixed-priority premises, then apply the new two-premise theorem. The
corpus records this as two linked arguments, not a new independent floor. -/
theorem noSelfOriginFromExercise {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (Prior : Sum Being Exercise → Sum Being Exercise → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces)
    (hBearer : BearerPrior Occurs bearer Prior)
    (hProduct : ProductPrior Occurs produces Prior)
    (hIrreflexive : IrreflexivePriority Prior)
    (hTransitive : TransitivePriority Prior) :
    NothingOriginatesItself F := by
  have hNoSelf := TruthCore.Results.Causality.ExistentialSelfActualization.noSelf
    Occurs bearer produces Prior hBearer hProduct hIrreflexive hTransitive
  exact noSelfOriginFromNoSelfProduction F Occurs bearer produces hOrigin hNoSelf

/-- Unregistered check of the weaker structural route recorded in
`docs/notes/unique-feedback-explanation-311.md`: asymmetry of the one supplied
mixed priority, with `BearerPrior` and `ProductPrior`, already excludes an
occurring exercise producing its own bearer's existence. Asymmetry is an OPEN
premise here, like the other priority laws; this is not a corpus result. -/
theorem noSelfProductionOfAsymmetric {Being Exercise : Type}
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (Prior : Sum Being Exercise → Sum Being Exercise → Prop)
    (hBearer : BearerPrior Occurs bearer Prior)
    (hProduct : ProductPrior Occurs produces Prior)
    (hAsymm : ∀ p q, Prior p q → ¬ Prior q p) :
    NoSelfProduction Occurs bearer produces :=
  fun a hOccurs hSelf =>
    hAsymm _ _ (hBearer a hOccurs) (hProduct a (bearer a) hOccurs hSelf)

/-- The asymmetry route composed with the origin-to-exercise bridge. -/
theorem noSelfOriginFromAsymmetric {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (Prior : Sum Being Exercise → Sum Being Exercise → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces)
    (hBearer : BearerPrior Occurs bearer Prior)
    (hProduct : ProductPrior Occurs produces Prior)
    (hAsymm : ∀ p q, Prior p q → ¬ Prior q p) :
    NothingOriginatesItself F :=
  noSelfOriginFromNoSelfProduction F Occurs bearer produces hOrigin
    (noSelfProductionOfAsymmetric Occurs bearer produces Prior hBearer hProduct hAsymm)

/-- Irreflexivity and transitivity of the mixed priority imply asymmetry. -/
theorem asymmetricOfIrreflexiveTransitive {Being Exercise : Type}
    (Prior : Sum Being Exercise → Sum Being Exercise → Prop)
    (hIrreflexive : IrreflexivePriority Prior)
    (hTransitive : TransitivePriority Prior) :
    ∀ p q, Prior p q → ¬ Prior q p :=
  fun p q hpq hqp => hIrreflexive p (hTransitive p q p hpq hqp)

/-- A directed three-cycle on bearer tokens, used to show that asymmetry is
strictly weaker than irreflexivity plus transitivity. -/
def threeCycle : Sum (Fin 3) Empty → Sum (Fin 3) Empty → Prop
  | .inl i, .inl j => j.val = (i.val + 1) % 3
  | _, _ => False

/-- The three-cycle is asymmetric but not transitive. -/
theorem threeCycle_asymmetric_not_transitive :
    (∀ p q, threeCycle p q → ¬ threeCycle q p) ∧
      ¬ TransitivePriority threeCycle := by
  refine ⟨?_, ?_⟩
  · intro p q
    cases p with
    | inr e => exact e.elim
    | inl i =>
      cases q with
      | inr e => exact e.elim
      | inl j =>
        show j.val = (i.val + 1) % 3 → ¬ i.val = (j.val + 1) % 3
        revert i j
        decide
  · intro hTrans
    have h01 : threeCycle (.inl 0) (.inl 1) := by
      show (1 : Fin 3).val = ((0 : Fin 3).val + 1) % 3
      decide
    have h12 : threeCycle (.inl 1) (.inl 2) := by
      show (2 : Fin 3).val = ((1 : Fin 3).val + 1) % 3
      decide
    have h02 : threeCycle (.inl 0) (.inl 2) := hTrans _ _ _ h01 h12
    have hNot : ¬ ((2 : Fin 3).val = ((0 : Fin 3).val + 1) % 3) := by decide
    exact hNot h02

end TruthCore.Results.Causality.OriginExerciseBridge
