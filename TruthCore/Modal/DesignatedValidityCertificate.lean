module

public import TruthCore.Modal.DesignatedValidity
public import TruthCore.Modal.ActualistDomainsCertificate
public import TruthCore.Explanation.ActualWorldGap

@[expose] public section

namespace TruthCore.Modal.DesignatedValidity
open TruthCore.German.Kant.CosmologicalInference

/-- The SAME old populated universal-frame ontology in both controls.
The policy changes from existence-restricted to unrestricted; its ontology,
identity, domain variation, and accessibility never change. -/
def Controls : Prop :=
  let m := TruthCore.Models.PSR.ContingentOnly.model.ontic
  let P := fun e => m.ExistsAt e true
  let D := fun a => m.ExistsAt a true
  (∀ a v, m.frame.access a v) ∧ (∀ a, m.ExistsAt a false) ∧
  NecessaryAt m false false ∧ ContingentAt m false true ∧
  ¬ ActualistDomains.IncreasingDomains m ∧ ¬ ActualistDomains.DecreasingDomains m ∧
  DiagonalValid D (fun _ e => P e) ∧
  ContentTransport m.frame D (fun _ e => P e) ∧
  ¬ SuccessorClosed m.frame D ∧ ¬ NecessitatedValid m.frame D (fun _ e => P e) ∧
  SuccessorClosed m.frame (fun _ => True) ∧
  IndependentRule m.frame (fun _ => True) ∧
  DiagonalValid (fun _ => True) (Agreement P) ∧
  ¬ ContentTransport m.frame (fun _ => True) (Agreement P) ∧
  ¬ NecessitatedValid m.frame (fun _ => True) (Agreement P)

/-- Exact generic correspondences, sufficient supplied-content transport,
ordinary Holds/Valid fragment, explicit empty-policy case, SAME-ontology
controls, and a composition of the old complete-history diagonal/rigid result.
No theorem proves a policy true of reality or adequacy of a proof calculus. -/
def Certificate : Prop :=
  (∀ (W : Type) (frame : Frame W) (D : W → Prop),
    IndependentRule frame D ↔ SuccessorClosed frame D) ∧
  (∀ (W : Type) (frame : Frame W) (D : W → Prop) (F : W → W → Prop),
    SuccessorClosed frame D → ContentTransport frame D F →
    DiagonalValid D F → NecessitatedValid frame D F) ∧
  (∀ (W : Type) (frame : Frame W) (D : W → Prop),
    UnrestrictedRule frame D ↔ IdentitySuccessors frame D) ∧
  (∀ (W : Type) (frame : Frame W) (D : W → Prop),
    AgreementRule frame D ↔ IdentitySuccessors frame D) ∧
  (∀ (W A : Type) (frame : Frame W) (D : W → Prop), SuccessorClosed frame D →
    ∀ (valuation : Valuation W A) (φ : Formula A),
      DiagonalValid D (fun _ e => Holds frame valuation e φ) →
      NecessitatedValid frame D (fun _ e => Holds frame valuation e φ)) ∧
  (∀ (W A : Type) (frame : Frame W) (φ : Formula A),
    Valid frame φ → Valid frame (.box φ)) ∧
  (∀ (W : Type) (frame : Frame W), UnrestrictedRule frame (fun _ => False)) ∧
  Controls ∧
  (∀ (W B T F : Type) (c : TruthCore.Explanation.ActualWorldGap.Case W B T F)
    (a b : W), TruthCore.Explanation.ActualWorldGap.Rival c.history a b →
    DiagonalValid (fun _ => True) (fun actual e => c.holds e (c.total actual)) ∧
    ¬ NecessitatedValid c.history.ontic.frame (fun _ => True)
      (fun actual e => c.holds e (c.total actual)))

end TruthCore.Modal.DesignatedValidity
