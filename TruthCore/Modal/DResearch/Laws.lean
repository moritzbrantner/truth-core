import TruthCore.Modal.ResearchFinite

/-! Mathematical D-frame experiments for #263. These are stipulated Kripke
semantics, not historical attributions or claims of metaphysical possibility.
The proposition domain, root and any identity criterion remain explicit. -/
namespace TruthCore.Modal.DResearch
open TruthCore.Modal.ResearchFixture
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)
universe u

/-- Seriality rules out every empty successor set, including at an MC world.
Identity admissibility is the exact additional scope assumption used here. -/
def SerialIdentityLaw : Prop :=
  ∀ (W : Type) (F : Frame W) (D : Domain W) w,
    Serial F → IdentityAdmissible D w → MC F D w → F.access w w

/-- In D, full MC means exactly a nonempty singleton successor set {w}.
This does not say that the whole type of worlds has only one member. -/
def FullCharacterizationLaw : Prop :=
  ∀ (W : Type) (F : Frame W) w, Serial F →
    (MC F allPredicates w ↔
      (F.access w w ∧ ∀ v, F.access w v → v = w))

/-- The alternative restricted-domain route uses all three explicit premises;
it does not identify language-indistinguishable states without extensionality. -/
def RestrictedIdentityLaw : Prop :=
  ∀ (W : Type) (F : Frame W) (D : Domain W) w,
    Serial F → TruthCore.Logic.ExcludedMiddle →
    (∀ P, D P → D (fun v => ¬ P v)) → PropositionalExtensionality D →
    MC F D w → F.access w w

/-- Seriality makes true admissible propositions at a collapse world possible,
and makes necessary collapse possible. No converse or propagation is asserted. -/
def NonvacuityLaw : Prop :=
  (∀ (W : Type) (F : Frame W) (D : Domain W) w (P : MProp W),
    Serial F → MC F D w → D P → P w → Dia F P w) ∧
  (∀ (W : Type) (F : Frame W) (D : Domain W) w,
    Serial F → Box F (MC F D) w → Dia F (MC F D) w) ∧
  (∀ (W : Type) (F : Frame W) w,
    Serial F → ¬ Box F (fun _ => False) w)

/-- Actual full collapse excludes a contingent predicate at that same root.
Seriality is not needed for this clause: both possibilities supply successors. -/
def ActualContingencyLaw : Prop :=
  ∀ (W : Type) (F : Frame W) w (P : MProp W),
    MC F allPredicates w → ¬ Contingent F P w

/-- Exact general D contract. Quantified hypotheses are not corpus axioms. -/
def LawChecks : Prop := SerialIdentityLaw ∧ FullCharacterizationLaw ∧
  RestrictedIdentityLaw ∧ NonvacuityLaw ∧ ActualContingencyLaw

end TruthCore.Modal.DResearch
