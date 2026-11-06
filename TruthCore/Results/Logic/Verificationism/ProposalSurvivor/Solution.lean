module

public import TruthCore.Logic.Verificationism.Proposal
public import TruthCore.Results.Logic.CorrectionCriterion.Solution

@[expose] public section
namespace TruthCore.Results.Logic.Verificationism.ProposalSurvivor

open TruthCore.Logic.Verificationism
open TruthCore.Logic.Verificationism.Proposal
open TruthCore.Logic.CorrectionCriterion
open TruthCore.Results.Logic.Verificationism.VerdictSilent

/-- Membership is exactly preservation by the retained representation. -/
theorem admitted_iff_fixed (f : Framework) (s : Content) :
    Admitted f s ↔ ∀ w, s w = s (encode f w) := by
  cases f with
  | expanded => exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | empirical =>
    constructor
    · intro h w
      have split : ∀ a b : Bool, (a && b) = true → a = true ∧ b = true := by
        intro a b hh
        cases a <;> cases b
        · exact False.elim (Bool.noConfusion hh)
        · exact False.elim (Bool.noConfusion hh)
        · exact False.elim (Bool.noConfusion hh)
        · exact ⟨rfl, rfl⟩
      have hs := split _ _ h
      have hs0 := beq_iff_eq.mp hs.1
      have hs1 := beq_iff_eq.mp hs.2
      rcases w with ⟨a, b⟩
      cases a <;> cases b
      · rfl
      · exact hs0.symm
      · rfl
      · exact hs1.symm
    · intro h
      have h0 := beq_iff_eq.mpr (h (false, true)).symm
      have h1 := beq_iff_eq.mpr (h (true, true)).symm
      change ((_ == _) && (_ == _)) = true
      change (s (false, false) == s (false, true)) = true at h0
      change (s (true, false) == s (true, true)) = true at h1
      exact (congrArg (fun a => a && _) h0).trans
        ((congrArg (fun b => true && b) h1).trans rfl)

/-- Import the earlier exact-factorization theorem, rather than postulating
that every language has an adequate classifier. -/
theorem admitted_iff_adequate (f : Framework) (s : Content) :
    Admitted f s ↔ AdmitsCriterion (encode f) (fun w => s w = true) := by
  have factor := TruthCore.Results.Logic.CorrectionCriterion.characterization.1
    World World (encode f) (fun w => s w = true)
  constructor
  · intro admitted
    have fixed := (admitted_iff_fixed f s).mp admitted
    apply factor.mpr
    intro w v same
    change s w = true ↔ s v = true
    have eq := (fixed w).trans ((congrArg s same).trans (fixed v).symm)
    exact ⟨fun h => eq ▸ h, fun h => eq.symm ▸ h⟩
  · intro adequate
    apply (admitted_iff_fixed f s).mpr
    intro w
    have invariant := factor.mp adequate
    have idem : encode f w = encode f (encode f w) := by cases f <;> rfl
    have same := invariant w (encode f w) idem
    change (s w = true ↔ s (encode f w) = true) at same
    have boolEq : ∀ a b : Bool, (a = true ↔ b = true) → a = b := by
      intro a b h
      cases a <;> cases b
      · rfl
      · exact False.elim (Bool.noConfusion (h.mpr rfl))
      · exact False.elim (Bool.noConfusion (h.mp rfl))
      · rfl
    exact boolEq _ _ same

theorem expressiveBoundary : ExpressiveBoundary := by
  refine ⟨admitted_iff_adequate, ?_, ?_, ?_, ?_⟩
  · intro f s hs
    apply (admitted_iff_fixed f _).mpr
    intro w
    change (!s w) = (!s (encode f w))
    rw [(admitted_iff_fixed f s).mp hs w]
  · intro f s t hs ht
    apply (admitted_iff_fixed f _).mpr
    intro w
    change (s w && t w) = (s (encode f w) && t (encode f w))
    rw [(admitted_iff_fixed f s).mp hs w, (admitted_iff_fixed f t).mp ht w]
  · intro f s t hs ht
    apply (admitted_iff_fixed f _).mpr
    intro w
    change (s w || t w) = (s (encode f w) || t (encode f w))
    rw [(admitted_iff_fixed f s).mp hs w, (admitted_iff_fixed f t).mp ht w]
  · intro f s hs
    apply (admitted_iff_fixed f s).mpr
    intro w
    exact (hs w).trans (hs (encode f w)).symm

theorem empirical_adequate (t : Task) : Adequate .empirical t ↔ t = .observedQuestion := by
  cases t with
  | observedQuestion =>
    exact ⟨fun _ => rfl, fun _ => (admitted_iff_adequate .empirical _).mp rfl⟩
  | hiddenQuestion =>
    constructor
    · intro h
      have impossible := (admitted_iff_adequate .empirical _).mpr h
      exact False.elim (Bool.noConfusion impossible)
    · intro h; cases h

theorem expanded_adequate (t : Task) : Adequate .expanded t := by
  exact (admitted_iff_adequate .expanded _).mp rfl

theorem adopted_observed (f : Framework) :
    Adopted .observedQuestion f ↔ f = .empirical := by
  cases f with
  | empirical =>
    refine ⟨fun _ => rfl, fun _ => ⟨(empirical_adequate _).mpr rfl, ?_⟩⟩
    intro g _; cases g <;> decide
  | expanded =>
    constructor
    · intro h
      have bad := h.2 .empirical ((empirical_adequate _).mpr rfl)
      exact absurd bad (by decide)
    · intro h; cases h

theorem adopted_hidden (f : Framework) :
    Adopted .hiddenQuestion f ↔ f = .expanded := by
  cases f with
  | empirical =>
    constructor
    · intro h; cases (empirical_adequate _).mp h.1
    · intro h; cases h
  | expanded =>
    refine ⟨fun _ => rfl, fun _ => ⟨expanded_adequate _, ?_⟩⟩
    intro g hg
    cases g with
    | empirical => cases (empirical_adequate _).mp hg
    | expanded => exact Nat.le_refl _

theorem pragmaticBoundary : PragmaticBoundary :=
  ⟨empirical_adequate, expanded_adequate, adopted_observed, adopted_hidden,
    fun _ h => h⟩

theorem semanticControls : SemanticControls := by
  have excluded : ¬ Admitted .empirical hidden := Bool.noConfusion
  have falseHidden : ¬ twoCoordinate.holds (false, false) hidden := Bool.noConfusion
  refine ⟨rfl, rfl, excluded, ?_, rfl, rfl, rfl, rfl,
    rfl, falseHidden, Bool.noConfusion, rfl, ?_, ?_, ?_⟩
  · exact Bool.noConfusion
  · intro rejects
    exact rejects hidden excluded (false, true) rfl
  · intro universal
    exact absurd (universal hidden) excluded
  · exact ⟨(adopted_observed _).mpr rfl, rfl, falseHidden⟩

/-- Joint nonvacuous model of the declared V4-style pragmatic proposal reading,
with exact task adequacy, Boolean membership and independent ambient truth. -/
theorem certificate : JointSurvivor :=
  ⟨expressiveBoundary, pragmaticBoundary, semanticControls, criterionVerdictSilentOnTruth⟩

end TruthCore.Results.Logic.Verificationism.ProposalSurvivor
