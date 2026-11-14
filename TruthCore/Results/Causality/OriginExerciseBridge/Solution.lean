module

public import TruthCore.Causality.OriginExerciseBridge
public import TruthCore.Causality.ExistentialSelfActualization
public import TruthCore.Results.Causality.ExistentialSelfActualization.Solution

@[expose] public section

namespace TruthCore.Results.Causality.OriginExerciseBridge

open TruthCore.Causality.TermSenseForks
open TruthCore.Causality.OriginExerciseBridge
open TruthCore.Causality.ExistentialSelfActualization

/-- If every origin-cause edge has an exercise of its source producing the
target's existence, an existing prohibition on productive self-actualization
excludes self-origin. This result has TWO explicit premises: the new bridge
and the independently recorded NoSelfProduction statement. That latter
statement already has a certified route from four open priority premises.
Nothing defines CausesOrigin as irreflexive. -/
theorem noSelfOriginFromNoSelfProduction {Being Respect Exercise : Type}
    (F : CauseFrame Being Respect)
    (Occurs : Exercise → Prop) (bearer : Exercise → Being)
    (produces : Exercise → Being → Prop)
    (hOrigin : OriginHasProductiveExercise F Occurs bearer produces)
    (hNoSelf : NoSelfProduction Occurs bearer produces) :
    NothingOriginatesItself F := by
  intro x hCausesOrigin
  obtain ⟨a, hOccurs, hBearerEq, hProduces⟩ := hOrigin x x hCausesOrigin
  have hProducesBearer : produces a (bearer a) := by
    simpa [hBearerEq] using hProduces
  exact hNoSelf a hOccurs hProducesBearer

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
