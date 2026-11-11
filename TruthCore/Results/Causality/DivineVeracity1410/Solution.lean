module

public import Mathlib.Logic.Function.Defs
public import TruthCore.Causality.DivineVeracity1410

/-! Exact conditional support options. Source warrant and application remain open. -/
@[expose] public section
namespace TruthCore.Results.Causality.DivineVeracity1410
open TruthCore.Case.Catholicism
open TruthCore.Case.Catholicism.StageThree.DivineFounding
open TruthCore.Causality.NamingVeracityBatch1
open TruthCore.Causality.DivineVeracity1410

/-- Introduce one speaker and proposition; specialize sincerity and then accuracy. No factivity of Knows. -/
theorem assertionTruthA (σ : Signature) (V : Veracity σ)
    (h0 : GodSincere σ V)
    (h1 : GodAssentAccurate σ V)
    : GodAssertsOnlyTruth σ V :=
  fun g hg hc p ha => h1 g hg hc p (h0 g hg hc p ha)

/-- Classically assume not-p; truth-completeness gives assent to not-p, contradicting no contrary assertion. No sincerity or general consistency is assumed. -/
theorem assertionTruthB (σ : Signature) (V : Veracity σ)
    (h0 : GodCounterAssertionComplete σ V)
    (h1 : GodNoContraryAssertion σ V)
    : GodAssertsOnlyTruth σ V :=
  by
    intro g hg hc p ha
    exact Classical.byContradiction (fun hn => h1 g hg hc p ha (h0 g hg hc p ha hn))

/-- Restrict the unrestricted OPEN completeness claim to actual assertions. -/
theorem completenessWeakens (σ : Signature) (V : Veracity σ)
    (h0 : GodTruthComplete σ V) : GodCounterAssertionComplete σ V :=
  fun g hg hc p _ hn => h0 g hg hc (¬ p) hn

/-- Classically a false assent to p would pair with assent to true not-p. This stronger cognitive branch is separate from minimal Route B. -/
theorem accuracyFromCompleteConsistent (σ : Signature) (V : Veracity σ)
    (h0 : GodTruthComplete σ V)
    (h1 : GodAssentConsistent σ V)
    : GodAssentAccurate σ V :=
  by
    intro g hg hc p hp
    exact Classical.byContradiction (fun hn => h1 g hg hc p hp (h0 g hg hc (¬ p) hn))

/-- Apply the OPEN permission applicability and OPEN positive endorsement norm. Forbidding lies alone is insufficient. -/
theorem sincerityFromNorms (σ : Signature) (V : Veracity σ) (G : Grounds σ)
    (h0 : GodAssertionsPermitted σ V G)
    (h1 : PermittedAssertionEndorsed σ V G)
    : GodSincere σ V :=
  fun g hg hc p ha => h1 g p (h0 g hg hc p ha)

/-- A genuinely asserted proposition is permitted; opposed assent would make that assertion impermissible. Beneficial-deception rivals contest the second premise. -/
theorem noContraryFromNorms (σ : Signature) (V : Veracity σ) (G : Grounds σ)
    (h0 : GodAssertionsPermitted σ V G)
    (h1 : ContraryAssertionImpermissible σ V G)
    : GodNoContraryAssertion σ V :=
  fun g hg hc p ha hn => h1 g p hn (h0 g hg hc p ha)

/-- Classically a false actual assent would instantiate the forbidden cognitive defect. Non-discursiveness alone is not a premise. -/
theorem accuracyFromDefects (σ : Signature) (V : Veracity σ) (G : Grounds σ)
    (h0 : FalseAssentDefective σ V G)
    (h1 : GodDefectFree σ V G)
    : GodAssentAccurate σ V :=
  by
    intro g hg hc p hp
    exact Classical.byContradiction (fun hn => h1 g hg hc p (h0 g p hp hn))

/-- Every truth is actually present to the same intellect; actual access and propositional assent bridges yield completeness. No capacity-to-actuality inference. -/
theorem completenessFromActualCognition (σ : Signature) (V : Veracity σ) (G : Grounds σ)
    (h0 : GodTruthPresent σ V G)
    (h1 : PresenceApprehended σ V G)
    (h2 : ApprehensionAssented σ V G)
    : GodTruthComplete σ V :=
  fun g hg hc p hp => h2 g p (h1 g p (h0 g hg hc p hp))

/-- Compose actual assent with the separate OPEN assent-to-held-known bridge; no new factivity. -/
theorem oldKnowingFromAssent (σ : Signature) (V : Veracity σ)
    (h0 : GodSincere σ V)
    (h1 : GodAssentHeldKnown σ V)
    : GodAssertsOnlyWhatHeKnows σ V :=
  fun g hg hc p ha => h1 g hg hc p (h0 g hg hc p ha)

/-- Pair sincerity and assent-to-held-known for the same speaker. This is an alternative support of the existing bridge, not its discharge. -/
theorem oldAttributeFromAssent (σ : Signature) (V : Veracity σ)
    (h0 : GodSincere σ V)
    (h1 : GodAssentHeldKnown σ V)
    : ClassicalAttributesIncludePerfectIntellectAndGoodWill σ V :=
  fun g hg hc => ⟨h0 g hg hc, h1 g hg hc⟩

/-- Confirmation counts as genuine assertion by the existing OPEN universal bridge; assertion truth then yields the exact existing GodConfirmsOnlyTruth endpoint. -/
theorem confirmsFromAssertion (σ : Signature) (V : Veracity σ) (A : Agency σ)
    (h0 : ConfirmingIsAsserting σ A V)
    (h1 : GodAssertsOnlyTruth σ V)
    : GodConfirmsOnlyTruth σ A :=
  fun g hg hc p hp => h1 g hg hc p (h0 g p hp)

theorem controls : TruthCore.Causality.DivineVeracity1410.Control.Certificate := by
  classical
  constructor
  · refine ⟨rfl, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [GodAssertionsPermitted, PermittedAssertionEndorsed,
      ContraryAssertionImpermissible, FalseAssentDefective, GodDefectFree,
      GodTruthPresent, PresenceApprehended, ApprehensionAssented,
      GodAssentHeldKnown, GodTruthComplete, GodAssentConsistent,
      TruthCore.Causality.DivineVeracity1410.Control.v, TruthCore.Causality.DivineVeracity1410.Control.grounds, TruthCore.Causality.NamingVeracityBatch1.Control.veracity]
  constructor
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨TruthCore.Causality.DivineVeracity1410.Control.v (fun _ => True) id, ?_, ?_⟩
      · exact fun _ _ _ _ hp => hp
      · intro h; exact h true rfl trivial False trivial
    · refine ⟨TruthCore.Causality.DivineVeracity1410.Control.v (fun _ => True) (fun _ => True), ?_, ?_⟩
      · exact fun _ _ _ _ _ => trivial
      · intro h; exact h true rfl trivial False trivial
    · refine ⟨TruthCore.Causality.DivineVeracity1410.Control.v (fun _ => True) (fun _ => False), ?_, ?_⟩
      · exact fun _ _ _ _ _ hn => hn
      · intro h; exact h true rfl trivial False trivial
    · refine ⟨TruthCore.Causality.DivineVeracity1410.Control.v (fun _ => True) id, ?_, ?_, ?_, ?_⟩
      · exact fun _ _ _ _ hp => hp
      · exact fun _ _ _ _ hp => hp
      · exact fun _ _ _ _ hp hn => hn hp
      · intro h; exact h true rfl trivial False trivial
    · refine ⟨TruthCore.Causality.DivineVeracity1410.Control.v (fun _ => True) (fun _ => False), ?_, ?_⟩
      · exact fun _ _ _ _ _ hn => hn
      · intro h; exact h true rfl trivial True trivial
  · let V := TruthCore.Causality.DivineVeracity1410.Control.v (fun _ => True) id
    let G : Grounds TruthCore.Causality.DivineVeracity1410.Control.σ := ⟨fun _ _ => True, fun _ p => ¬ p, fun _ p => p, fun _ p => p⟩
    refine ⟨V, G, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun _ _ _ _ hp => hp
    · exact fun _ _ _ _ hp => hp
    · exact fun _ _ _ _ hp hn => hn hp
    · exact fun _ _ _ _ _ => trivial
    · intro h; exact h true False (fun h => h) trivial
    · intro h; exact h true rfl trivial False trivial

end TruthCore.Results.Causality.DivineVeracity1410
