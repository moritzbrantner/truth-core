import TruthCore.Logic.TruthNontriviality
import TruthCore.Results.Logic.TruthNontriviality.PropositionalCollapse.Solution
import TruthCore.Results.Logic.Relativism.SelfFalsifying.Solution
namespace TruthCore.Results.Logic.TruthNontriviality.Core
open TruthCore.Logic.SelfApplication
open TruthCore.Logic.Relativism
open TruthCore.Logic.TruthPilot
open TruthCore.Logic.TruthNontriviality

theorem not_collapse_of_expressive {Content : Type} {truth : Content → Prop}
    (hExpr : Expressive truth) : ¬ Collapse truth := by
  intro hCollapse
  apply PropositionalCollapse.noGlobalPropositionalCollapse
  intro P Q
  obtain ⟨c, hc⟩ := hExpr P
  obtain ⟨d, hd⟩ := hExpr Q
  exact hc.symm.trans ((hCollapse c d).trans hd)

theorem collapse_of_allFail {Content : Type} {truth : Content → Prop}
    (h : AllFail truth) : Collapse truth :=
  fun p q => ⟨fun hp => (h p hp).elim, fun hq => (h q hq).elim⟩

/-- Predicate collapse reaches `Prop` only through `Expressive`; the negation
laws use the content's own negation and no witness from `Prop`. -/
theorem collapseLaws : CollapseLaws := by
  intro Content truth neg
  have hFail : Collapse truth → NegationRespected truth neg → AllFail truth :=
    fun hC hR p hp => hR p ((hC p (neg p)).1 hp) hp
  have hHold : Collapse truth → NegationExhaustive truth neg → AllHold truth := by
    intro hC hE p
    cases hE p with
    | inl h => exact h
    | inr h => exact (hC p (neg p)).2 h
  refine ⟨not_collapse_of_expressive,
    fun h p q => ⟨fun _ => h q, fun _ => h p⟩,
    collapse_of_allFail,
    ?_,
    fun p₀ hH hF => hF p₀ (hH p₀),
    hFail, hHold,
    fun p₀ hC hR hE => hFail hC hR p₀ (hHold hC hE p₀)⟩
  intro p₀ hC hDec
  cases hDec with
  | inl h => exact Or.inl fun p => (hC p₀ p).1 h
  | inr h => exact Or.inr fun p hp => h ((hC p p₀).1 hp)

/-- The thesis clause composes `thesisNotAbsolutelyTrue`: disquotation makes the
thesis not absolutely true, and capture then refutes the global denial. It does
not produce a witness of absolute truth. -/
theorem globalDenialPrice : GlobalDenialPrice := by
  intro Agent Content T
  refine ⟨fun hG => ⟨collapse_of_allFail hG, fun hE => not_collapse_of_expressive hE
      (collapse_of_allFail hG)⟩, ?_, ?_, ?_, ?_⟩
  · intro neg p₀ hG hE
    cases hE p₀ with
    | inl h => exact hG _ h
    | inr h => exact hG _ h
  · intro thesis hSays hCapture hG
    exact Relativism.SelfFalsifying.thesisNotAbsolutelyTrue T (fun _ => True) thesis
      trivial hSays (hCapture hG)
  · intro hN s p
    cases s with
    | absolute => exact hN.1 p
    | relativeTo a => exact hN.2 a p
  · intro a hE hN
    exact not_collapse_of_expressive hE (collapse_of_allFail (hN.2 a))

/-- The collapse laws and the price of global denial. -/
theorem truthNontrivialityCore : TruthNontrivialityCore :=
  ⟨collapseLaws, globalDenialPrice⟩
end TruthCore.Results.Logic.TruthNontriviality.Core
