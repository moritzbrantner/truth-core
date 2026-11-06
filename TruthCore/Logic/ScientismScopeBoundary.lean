module
public import TruthCore.Logic.Scientism

/-! Analyst scope siblings. Generic ScopedScientism is not universal scientism.
The scope of all established claims is stronger than the scope of possible
nonempirical counterexamples. Neither scope condition is asserted as true. -/
@[expose] public section
namespace TruthCore.Logic.ScientismScopeBoundary
open TruthCore.Logic.Scientism

def AllEstablishedInScope {Claim : Type} (E : EpistemicFrame Claim)
    (scope : Claim → Prop) : Prop := ∀ c, E.established c → scope c

def NonEmpiricalWitnessesInScope {Claim : Type} (E : EpistemicFrame Claim)
    (scope : Claim → Prop) : Prop :=
  ∀ c, E.established c → ¬ E.empiricallyEstablished c → scope c

/-- Selected existential coverage sufficient for the guarded inference. It does
not require each nonempirical witness to be in scope. -/
def SomeNonEmpiricalWitnessInScope {Claim : Type} (E : EpistemicFrame Claim)
    (scope : Claim → Prop) : Prop :=
  SomeNonEmpiricalEstablished E →
    ∃ c, scope c ∧ E.established c ∧ ¬ E.empiricallyEstablished c

def NoNonEmpiricalEstablished {Claim : Type} (E : EpistemicFrame Claim) : Prop :=
  ¬ SomeNonEmpiricalEstablished E

def Controls : Prop :=
  (∃ (E : EpistemicFrame Bool) (scope : Bool → Prop),
    ScopedScientism E scope ∧ SomeNonEmpiricalEstablished E ∧
    (∃ c, scope c ∧ E.established c ∧ E.empiricallyEstablished c) ∧
    ¬ NonEmpiricalWitnessesInScope E scope) ∧
  (∃ (E : EpistemicFrame Bool) (scope : Bool → Prop),
    NonEmpiricalWitnessesInScope E scope ∧ ¬ AllEstablishedInScope E scope ∧
    SomeNonEmpiricalEstablished E) ∧
  (∃ (E : EpistemicFrame Bool) (scope : Bool → Prop),
    SomeNonEmpiricalWitnessInScope E scope ∧ ¬ NonEmpiricalWitnessesInScope E scope ∧
    SomeNonEmpiricalEstablished E)
end TruthCore.Logic.ScientismScopeBoundary
