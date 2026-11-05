module

public import TruthCore.Modal.DesignatedValidityCertificate
public import TruthCore.Results.Modal.ActualistDomains.Solution
public import TruthCore.Results.Explanation.ActualWorldGap.Solution

@[expose] public section

namespace TruthCore.Results.Modal.DesignatedValidity
open TruthCore.Modal
open TruthCore.Modal.DesignatedValidity

variable {W : Type}

theorem independent_iff (frame : Frame W) (D : W → Prop) :
    IndependentRule frame D ↔ SuccessorClosed frame D := by
  constructor
  · intro h
    exact h D (fun _ ha => ha)
  · intro h P hd a ha v hav
    exact hd v (h a ha v hav)

theorem of_transport (frame : Frame W) (D : W → Prop) (F : W → W → Prop)
    (hClosed : SuccessorClosed frame D) (hTransport : ContentTransport frame D F)
    (hValid : DiagonalValid D F) : NecessitatedValid frame D F := by
  intro a ha v hav
  exact hTransport a ha v hav (hValid v (hClosed a ha v hav))

theorem unrestricted_iff (frame : Frame W) (D : W → Prop) :
    UnrestrictedRule frame D ↔ IdentitySuccessors frame D := by
  constructor
  · intro h a ha v hav
    exact h (fun actual e => e = actual) (fun _ _ => rfl) a ha v hav
  · intro h F hd a ha v hav
    rw [h a ha v hav]
    exact hd a ha

theorem agreement_diagonal (D : W → Prop) (P : W → Prop) :
    DiagonalValid D (Agreement P) := by
  intro _ _
  exact Iff.rfl

theorem agreement_iff (frame : Frame W) (D : W → Prop) :
    AgreementRule frame D ↔ IdentitySuccessors frame D := by
  constructor
  · intro h a ha v hav
    exact (h (fun e => e = a) (agreement_diagonal D _) a ha v hav).mpr rfl
  · intro h P hd
    exact (unrestricted_iff frame D).mpr h (Agreement P) hd

/-- The ordinary object-language fragment has no actuality coordinate. Its
closed-policy rule is a specialization, not expressive completeness for F. -/
theorem holds_of_closed {A : Type} (frame : Frame W) (D : W → Prop)
    (hClosed : SuccessorClosed frame D) (valuation : Valuation W A) (φ : Formula A)
    (hValid : DiagonalValid D (fun _ e => Holds frame valuation e φ)) :
    NecessitatedValid frame D (fun _ e => Holds frame valuation e φ) := by
  exact (independent_iff frame D).mpr hClosed _ hValid

theorem global_necessitation {A : Type} (frame : Frame W) (φ : Formula A)
    (h : Valid frame φ) : Valid frame (.box φ) := by
  intro valuation _ v _
  exact h valuation v

theorem empty_policy (frame : Frame W) : UnrestrictedRule frame (fun _ => False) := by
  intro _ _ _ ha
  exact ha.elim

/-- Both failures use the same ontology, including its old domain failures.
The first keeps content transport but drops designation closure. The second
repairs closure and the independent rule but loses transport for Agreement. -/
theorem controls : Controls := by
  let m := TruthCore.Models.PSR.ContingentOnly.model.ontic
  let P := fun e => m.ExistsAt e true
  let D := fun a => m.ExistsAt a true
  have hp : P false := Or.inr ⟨rfl, rfl⟩
  have hn : ¬ P true := by
    rintro (h | ⟨h, _⟩)
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  have old := TruthCore.Results.Modal.ActualistDomains.checks.2.2.2
  have hClosed : SuccessorClosed m.frame (fun _ => True) := fun _ _ _ _ => True.intro
  refine ⟨old.1, fun _ => Or.inl rfl, old.2.1,
    TruthCore.Models.PSR.ContingentOnly.evaluation2,
    old.2.2.2.1, old.2.2.2.2.1,
    fun _ ha => ha, fun _ _ _ _ h => h, ?_, ?_, hClosed,
    (independent_iff m.frame _).mpr hClosed, agreement_diagonal _ P, ?_, ?_⟩
  · intro h
    exact hn (h false hp true True.intro)
  · intro h
    exact hn (h false hp true True.intro)
  · intro h
    exact hn ((h false True.intro true True.intro Iff.rfl).mpr hp)
  · intro h
    exact hn ((h false True.intro true True.intro).mpr hp)

/-- Compose the old #751 boundary into a rule counterinstance; the diagonal
and rigid-total facts themselves are imported, not advertised as new. -/
theorem history_rule_failure {B T F : Type}
    (c : TruthCore.Explanation.ActualWorldGap.Case W B T F) (a b : W)
    (hRival : TruthCore.Explanation.ActualWorldGap.Rival c.history a b) :
    DiagonalValid (fun _ => True) (fun actual e => c.holds e (c.total actual)) ∧
    ¬ NecessitatedValid c.history.ontic.frame (fun _ => True)
      (fun actual e => c.holds e (c.total actual)) := by
  constructor
  · intro actual _
    exact TruthCore.Results.Explanation.ActualWorldGap.refl_total c actual
  · intro h
    exact TruthCore.Results.Explanation.ActualWorldGap.rival_not_total c hRival
      (h a True.intro b hRival.1)

theorem checks : Certificate := by
  exact ⟨fun _ => independent_iff, fun _ => of_transport,
    fun _ => unrestricted_iff, fun _ => agreement_iff,
    fun _ _ => holds_of_closed, fun _ _ => global_necessitation,
    fun _ => empty_policy, controls, fun _ _ _ _ => history_rule_failure⟩

end TruthCore.Results.Modal.DesignatedValidity
