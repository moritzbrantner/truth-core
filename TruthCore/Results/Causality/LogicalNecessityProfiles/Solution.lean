module

public import TruthCore.Causality.LogicalNecessityProfiles

/-! Conditional comparisons and the explicit same-bearer root bridge. -/
@[expose] public section
namespace TruthCore.Results.Causality.LogicalNecessityProfiles
open TruthCore.Modal
open TruthCore.Causality.NecessarySenseFork
open TruthCore.Causality.LogicalNecessityProfiles
open TruthCore.German.Kant.CosmologicalInference (Ontic)
open TruthCore.Causality.BruteFoundationBoundary (Profile)
open TruthCore.Case.Catholicism (Signature)

/-- Exact strong-only-premise weakening on the same formula. -/
theorem kToFrame {W A : Type} (F : Frame W) (φ : Formula A)
    (h : AllFrameKValidity φ) : SelectedFrameValidity F φ := h W F

/-- Exact strong-only-premise weakening; theory need not be consistent. -/
theorem frameToTheory {W A : Type} (F : Frame W) (Γ : Formula A → Prop) (φ : Formula A)
    (h : SelectedFrameValidity F φ) : TheoryRelativeEntailment F Γ φ := by
  intro V w _
  exact h V w

/-- Selected-model admission at each consumed point is explicit. -/
theorem theoryToTrueAndBox {W A : Type} (F : Frame W) (Γ : Formula A → Prop)
    (φ : Formula A) (V : Valuation W A) (w : W)
    (h : TheoryRelativeEntailment F Γ φ) (hc : TheoryOnCone F V w Γ) :
    TrueAndBox F V w φ := ⟨h V w hc.1, fun v hv => h V v (hc.2 v hv)⟩

/-- Joint satisfiability excludes explosion to falsum. -/
theorem jointModelNotFalsum {W A : Type} (F : Frame W) (Γ : Formula A → Prop)
    (hm : JointModel F Γ) : NoFalsumConsequence F Γ := by
  intro h
  obtain ⟨V, w, hw⟩ := hm
  exact h V w hw

/-- Bridge to the existing root-route node. RootFacts remains independently
supplied for the SAME bearer; nothing is inferred from a nonempty carrier. -/
theorem theoryToRoot {W A : Type} (σ : Signature) (m : Profile W σ.Being)
    (w : W) (n : σ.Being) (CN : σ.Being → σ.Being → Prop)
    (Γ : Formula A → Prop) (φ : Formula A) (V : Valuation W A)
    (h : TheoryRelativeEntailment m.ontic.frame Γ φ)
    (hc : TheoryOnCone m.ontic.frame V w Γ)
    (hd : ExistenceDictionary m.ontic V φ n)
    (hr : RootFactsForBearer σ m w n) : NecessaryRootBoxK σ m w CN := by
  refine ⟨n, ?_, hr⟩
  intro v hv
  exact (hd v).mp (h V v (hc.2 v hv))

/-- Finite nonvacuity and strictness/omission witnesses. -/
theorem controls : Fixture.Controls := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro V w h
      exact h () True.intro
    · intro h
      exact h Unit Fixture.dead Fixture.falseV () (fun _ he => False.elim he)
  · constructor
    · intro V w h
      exact h _ rfl
    · exact TruthCore.Causality.LogicalNecessityContrast.atom_not_valid _ ()
  · constructor
    · exact ⟨True.intro, fun _ _ => True.intro⟩
    · intro h
      exact h Fixture.falseV () (fun _ he => False.elim he)
  · constructor
    · intro φ V w h
      exact False.elim (h _ rfl)
    · rintro ⟨V, w, h⟩
      exact h _ rfl
  · refine ⟨⟨Fixture.trueV, (), ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro ψ hψ
      cases hψ
      trivial
    · intro ψ hψ
      cases hψ
      trivial
    · intro v _ ψ hψ
      cases hψ
      trivial
    · intro v
      exact Iff.rfl
    · exact ⟨⟨⟨True.intro, True.intro⟩, fun _ h => False.elim h.2.2⟩,
        True.intro, (fun _ _ => rfl), True.intro⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro V w h
      exact h _ rfl
    · intro ψ hψ
      cases hψ
      rfl
    · intro h
      exact Bool.noConfusion (h true ⟨rfl, rfl⟩)
  · constructor
    · intro V w h
      exact h _ rfl
    · intro h
      exact h.1
/-- Explicit omissions of the dictionary and independent God/root facts. -/
theorem omissionControls : Fixture.OmissionControls := by
  constructor
  · refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · intro V w _ hp
      exact hp
    · intro ψ hψ
      exact False.elim hψ
    · intro v _ ψ hψ
      exact False.elim hψ
    · exact ⟨⟨⟨True.intro, rfl⟩, fun _ h => False.elim h.2.2⟩,
        True.intro, (fun _ _ => rfl), True.intro⟩
    · intro hd
      exact Bool.noConfusion ((hd true).mp (fun hp => hp))
    · rintro ⟨n, hn, _⟩
      exact Bool.noConfusion (hn true ⟨rfl, rfl⟩)
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro V w h
      exact h _ rfl
    · constructor
      · intro ψ hψ
        cases hψ
        trivial
      · intro v _ ψ hψ
        cases hψ
        trivial
    · intro v
      exact Iff.rfl
    · rintro ⟨n, _, hr⟩
      exact hr.2.1
end TruthCore.Results.Causality.LogicalNecessityProfiles
