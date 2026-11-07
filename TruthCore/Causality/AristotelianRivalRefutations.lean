module

public import TruthCore.Alternatives.ActPotencyRegress
public import TruthCore.Greek.Aristotle.MetaphysicsIX
public import TruthCore.Greek.Aristotle.Physics

/-! Conditional refutations of two act/potency rivals from Aristotle's own
analyses

* The Scotist rival `STMT-ACT-AND-POTENCY-IN-SAME-RESPECT` (something is in act
  and in potency in the same respect) contradicts Metaphysics IX.6's analysis of
  potency as unactualized capacity (`PotencyIsUnactualizedCapacityReading`).
* The Ash'arite rival `STMT-MOVED-WITHOUT-POTENCY` (something is moved without
  being in potency) contradicts Physics III.1's analysis of being moved as the
  actualization of a potency (`BeingMovedIsActualizationOfPotencyReading`).

Each rival must therefore reject the corresponding Aristotelian analysis, not
merely the Prima Via premise derived from it. Conditional refutations; the
analyses stay open. -/

@[expose] public section

namespace TruthCore.Causality.AristotelianRivalRefutations
open TruthCore.Alternatives.ActPotencyRegress
  (InActAndPotencyInSameRespectReading MovedWithoutPotencyReading)

/-- The Scotist rival fails. -/
def NoActAndPotencyInSameRespect {B R : Type} (InAct InPotency : B → R → Prop) : Prop :=
  ¬ InActAndPotencyInSameRespectReading InAct InPotency

/-- The Ash'arite rival fails. -/
def NoMovedWithoutPotency {B R : Type} (MovedIn InPotency : B → R → Prop) : Prop :=
  ¬ MovedWithoutPotencyReading MovedIn InPotency

namespace Control
open TruthCore.Greek.Aristotle.Metaphysics (PotencyIsUnactualizedCapacityReading)
open TruthCore.Greek.Aristotle.Physics (BeingMovedIsActualizationOfPotencyReading)

def yes (_ _ : Unit) : Prop := True
def no (_ _ : Unit) : Prop := False

/-- Without the Aristotelian analyses, each rival is satisfiable; with them, each
fails (the analyses are themselves satisfiable). -/
def Certificate : Prop :=
  (¬ PotencyIsUnactualizedCapacityReading yes yes yes ∧
    InActAndPotencyInSameRespectReading yes yes) ∧
  (¬ BeingMovedIsActualizationOfPotencyReading yes no no ∧
    MovedWithoutPotencyReading yes no) ∧
  (PotencyIsUnactualizedCapacityReading yes no yes ∧
    BeingMovedIsActualizationOfPotencyReading no no no)

end Control
end TruthCore.Causality.AristotelianRivalRefutations
