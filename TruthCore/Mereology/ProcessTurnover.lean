import TruthCore.Mereology.Vitalism

/-! Analyst's process/material distinction, prompted by the river question.
No historical Heraclitus interpretation is claimed. A process carrier may have
changing constituents; giving it a *timeless* material extension is an extra
commitment. Reuses the existing two-cohort turnover fixture, not a new life or
substance predicate. -/
namespace TruthCore.Mereology.ProcessTurnover
open Vitalism

/-- The same carrier is assigned to operationally continuous phases. This is
an explicit persistence principle, not part of the meaning of Continuity. -/
def PreservesContinuity {P : Type} (s : Scenario) (carrier : Phase → P) : Prop :=
  ∀ p q, s.Continuity p q → carrier p = carrier q

/-- Timeless constituent representation: a carrier has one fixed extension.
This is stronger than time-indexed material constitution or materialism. -/
def FixedExtension {P : Type} (s : Scenario) (carrier : Phase → P)
    (parts : P → Component → Prop) : Prop :=
  ∀ p c, s.MemberAt p c ↔ parts (carrier p) c

/-- A single changed constituent defeats a fixed-extension representation
whenever the two phases have the same carrier. -/
theorem changed_member_no_fixed_extension {P : Type} (s : Scenario)
    (carrier : Phase → P) (parts : P → Component → Prop)
    (p q : Phase) (c : Component) (same : carrier p = carrier q)
    (present : s.MemberAt p c) (absent : ¬ s.MemberAt q c) :
    ¬ FixedExtension s carrier parts := by
  intro fixed
  apply absent
  apply (fixed q c).mpr
  rw [← same]
  exact (fixed p c).mp present

/-- The existing turnover profile already contains an original constituent
lost at the later phase and an operational continuation connecting the phases. -/
theorem turnover_excludes_fixed_extension {P : Type} (s : Scenario)
    (carrier : Phase → P) (parts : P → Component → Prop)
    (turnover : TurnoverProfile s) (persist : PreservesContinuity s carrier) :
    ¬ FixedExtension s carrier parts := by
  rcases turnover with ⟨old, _, _, lost, _, _, _, _, _, _, continued⟩
  exact changed_member_no_fixed_extension s carrier parts .early .late .original
    (persist _ _ continued) old lost

/-- Time-indexed constitution can represent a constant carrier throughout the
same turnover. This is a logical model, not an adequate theory of river identity. -/
def DynamicExtension {P : Type} (s : Scenario) (carrier : Phase → P)
    (parts : Phase → P → Component → Prop) : Prop :=
  ∀ p c, s.MemberAt p c ↔ parts p (carrier p) c

/-- Closed certificate: no fixed-extension interpretation preserves both the
fixture's turnover and its continuity as carrier identity; a time-indexed
interpretation does. A phase-carrier interpretation also preserves a fixed
extension but rejects that continuity-to-identity principle. -/
def Boundary : Prop :=
  (∀ (P : Type) (carrier : Phase → P) (parts : P → Component → Prop),
    PreservesContinuity (scenario False False) carrier →
      ¬ FixedExtension (scenario False False) carrier parts) ∧
  (∃ (carrier : Phase → Unit) (parts : Phase → Unit → Component → Prop),
    PreservesContinuity (scenario False False) carrier ∧
      DynamicExtension (scenario False False) carrier parts) ∧
  (∃ (carrier : Phase → Phase) (parts : Phase → Component → Prop),
    FixedExtension (scenario False False) carrier parts ∧
      ¬ PreservesContinuity (scenario False False) carrier)
end TruthCore.Mereology.ProcessTurnover
