module

public import TruthCore.Causality.PureIndiscernibility
public import TruthCore.Results.Causality.PureActThisness.Solution

@[expose] public section

namespace TruthCore.Results.Causality.PureIndiscernibility
open TruthCore.Case.Catholicism
open TruthCore.Causality.PureActThisness
open TruthCore.Causality.PureIndiscernibility
open TruthCore.Results.Causality.PureActThisness (pureActPluralityIsBare)

/-- Unrestricted perfection and strict pure actuality make any two first movers
really indiscernible and purely determined; the narrower bridge makes them one.
Conditional on three OPEN premises. No first mover is produced. -/
theorem uniqueFromPureIndiscernibility {B R D : Type}
    (Moved : B → R → Prop) (Moves : B → B → R → Prop)
    (Has : B → D → Prop) (Pure : D → Prop)
    (hEvery : FirstMoverHasEveryPureDetermination Moved Moves Has Pure)
    (hPure : FirstMoverDeterminationsArePure Moved Moves Has Pure)
    (hBridge : PurelyDeterminedIndiscerniblesIdentical Has Pure) :
    AtMostOneFirstUnmovedMover Moved Moves :=
  fun f g hf hg =>
    hBridge f g (hPure f hf) (pureActPluralityIsBare Moved Moves Has Pure hEvery hPure f g hf hg)

/-- Identity of real indiscernibles entails the narrower bridge. -/
theorem pureIndiscernibilityOfReal {B D : Type} (Has : B → D → Prop) (Pure : D → Prop)
    (hReal : RealDeterminationsIndividuate Has) :
    PurelyDeterminedIndiscerniblesIdentical Has Pure :=
  fun x y _ h => hReal x y h

section Controls
open TruthCore.Causality.PureIndiscernibility.Control
open TruthCore.Causality.PureActThisness.Control
open TruthCore.Causality.PartFreePlurality
open TruthCore.Results.Causality.PureActThisness
  (bareRival withoutStrictPurity withoutUnrestrictedPerfection individuationExceedsUniqueness
    thisIndividuates)
open TruthCore.Results.Causality.RootMultiplication (onlyG gFirst)

theorem spheres :
    FirstMoverHasEveryPureDetermination jMoved jMoves sphereHas spherePure ∧
    FirstMoverDeterminationsArePure jMoved jMoves sphereHas spherePure ∧
    PurelyDeterminedIndiscerniblesIdentical sphereHas spherePure ∧
    AtMostOneFirstUnmovedMover jMoved jMoves ∧
    IsFirstUnmovedMover jMoved jMoves (.g : JB) ∧
    ¬ RealDeterminationsIndividuate sphereHas := by
  refine ⟨?_, ?_, ?_, fun a b ha hb => (onlyG a ha).trans (onlyG b hb).symm, gFirst, ?_⟩
  · intro a ha d hd
    cases d with
    | false => exact hd.elim
    | true => exact onlyG a ha
  · intro a ha d hd
    cases d with
    | false => exact (hd (onlyG a ha)).elim
    | true => trivial
  · intro a b hp h
    cases a with
    | g => exact ((h true).1 rfl).symm
    | f => exact (hp false ((fun e => nomatch e))).elim
    | x => exact (hp false ((fun e => nomatch e))).elim
    | c => exact (hp false ((fun e => nomatch e))).elim
  · intro h
    have e : (.f : JB) = .x := h .f .x fun d => by
      cases d with
      | false => exact ⟨(fun _ e => nomatch e), (fun _ e => nomatch e)⟩
      | true => exact ⟨(fun e => nomatch e), (fun e => nomatch e)⟩
    exact nomatch e

theorem reach :
    FirstMoverHasEveryPureDetermination jMoved jMoves onlyGHas (fun _ => True) ∧
    FirstMoverDeterminationsArePure jMoved jMoves onlyGHas (fun _ => True) ∧
    AtMostOneFirstUnmovedMover jMoved jMoves ∧
    ¬ PurelyDeterminedIndiscerniblesIdentical onlyGHas (fun _ => True) := by
  obtain ⟨hU, hS, _, hA, _⟩ := individuationExceedsUniqueness
  refine ⟨hU, hS, hA, fun h => ?_⟩
  have e : (.f : JB) = .x :=
    h .f .x (fun _ _ => trivial) fun _ => ⟨(fun e => nomatch e), (fun e => nomatch e)⟩
  exact nomatch e

theorem equivalence : ∀ {B R D : Type} (Moved : B → R → Prop) (Moves : B → B → R → Prop)
      (Has : B → D → Prop) (Pure : D → Prop),
    FirstMoverHasEveryPureDetermination Moved Moves Has Pure →
    FirstMoverDeterminationsArePure Moved Moves Has Pure →
    OnlyFirstMoversPurelyDetermined Moved Moves Has Pure →
    (PurelyDeterminedIndiscerniblesIdentical Has Pure ↔ AtMostOneFirstUnmovedMover Moved Moves) := by
  intro B R D Moved Moves Has Pure hEvery hPure hOnly
  refine ⟨uniqueFromPureIndiscernibility Moved Moves Has Pure hEvery hPure, fun hA x y hx h => ?_⟩
  exact hA x y (hOnly x hx) (hOnly y fun d hy => hx d ((h d).2 hy))

theorem controls : TruthCore.Causality.PureIndiscernibility.Control.Certificate := by
  obtain ⟨bU, bS, _, _, _, bA⟩ := bareRival
  obtain ⟨sU, sS, _, sR, _, sA⟩ := withoutStrictPurity
  obtain ⟨uU, uS, _, uR, _, uA⟩ := withoutUnrestrictedPerfection
  exact ⟨spheres, reach, equivalence,
    ⟨bU, bS, fun h => bA (uniqueFromPureIndiscernibility moved moves actHas allPure bU bS h), bA⟩,
    ⟨sU, sS, pureIndiscernibilityOfReal thisHas actOnly sR, sA⟩,
    ⟨uU, uS, pureIndiscernibilityOfReal thisHas everyPure uR, uA⟩⟩

end Controls
end TruthCore.Results.Causality.PureIndiscernibility
