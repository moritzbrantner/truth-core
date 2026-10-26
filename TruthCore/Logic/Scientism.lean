import TruthCore.Logic.SelfApplication

/-!
Scientism as an instance of the self-application schema (#397).

The thesis is stated without attribution: modern defenders and critics are in
copyright and await bibliographic witnesses (#378). `EpistemicFrame` keeps two
predicates apart: being established (known, rationally warranted) and being
established by empirical evidence. Neither implies the other by definition.

* Strong scientism: within its scope, whatever is established is established
  empirically. If its own formulation is in scope and not empirically
  established, it is not both true and established (`ScientismDilemma`).
* Weak (restricted) scientism: the same norm restricted to a demarcated
  domain of questions. Its second-order test either collapses into the strong
  dilemma (formulation inside the domain) or concedes a non-empirically
  established claim (formulation outside it). Outside, it is consistent.
-/

namespace TruthCore.Logic.Scientism

open TruthCore.Logic.SelfApplication

variable {Claim : Type}

/-- Two epistemic predicates on claims, with no built-in relation. -/
structure EpistemicFrame (Claim : Type) where
  established : Claim → Prop
  empiricallyEstablished : Claim → Prop

/-- The scientistic norm: within scope, the standard is empirical establishment. -/
def scientismNorm (E : EpistemicFrame Claim) (scope : Claim → Prop) : Norm Claim :=
  ⟨scope, E.empiricallyEstablished⟩

/-- Scientism with explicit scope (`STMT-STRONG-SCIENTISM`): every established
claim in scope is empirically established. Strong scientism is the case where
every claim (every claim to knowledge) is in scope. -/
def ScopedScientism (E : EpistemicFrame Claim) (scope : Claim → Prop) : Prop :=
  (scientismNorm E scope).Holds E.established

/-- Scope premise: the scientistic thesis's own formulation is in its scope
(`STMT-SCIENTISM-IN-OWN-SCOPE`). -/
def ScientismInOwnScope (scope : Claim → Prop) (self : Claim) : Prop :=
  scope self

/-- The scientistic thesis is not itself established by empirical evidence
(`STMT-SCIENTISM-NOT-EMPIRICALLY-ESTABLISHED`). -/
def ScientismNotEmpiricallyEstablished (E : EpistemicFrame Claim) (self : Claim) : Prop :=
  ¬ E.empiricallyEstablished self

/-- The two horns (`STMT-STRONG-SCIENTISM-DILEMMA`): if scientism holds, its
own formulation is not established; if its formulation is established, it is
a counterexample and scientism fails. -/
def ScientismDilemma (E : EpistemicFrame Claim) (scope : Claim → Prop) (self : Claim) : Prop :=
  (ScopedScientism E scope → ¬ E.established self) ∧
    (E.established self → ¬ ScopedScientism E scope)

/-- Some established claim is not empirically established
(`STMT-SOME-NON-EMPIRICAL-ESTABLISHED`). -/
def SomeNonEmpiricalEstablished (E : EpistemicFrame Claim) : Prop :=
  ∃ c, E.established c ∧ ¬ E.empiricallyEstablished c

/-- Weak (restricted) scientism (`STMT-WEAK-SCIENTISM-RESTRICTED`): the
scientistic norm restricted to the domain fixed by a demarcation criterion. -/
def WeakScientism (E : EpistemicFrame Claim) (scope : Claim → Prop)
    (D : Norm.Demarcation Claim) : Prop :=
  ((scientismNorm E scope).restrict D).Holds E.established

/-- The weak thesis's own formulation lies in the strong scope
(`STMT-WEAK-SCIENTISM-IN-STRONG-SCOPE`). -/
def WeakThesisInStrongScope (scope : Claim → Prop) (w : Claim) : Prop :=
  scope w

/-- The weak thesis is not itself established by empirical evidence
(`STMT-WEAK-SCIENTISM-NOT-EMPIRICALLY-ESTABLISHED`). -/
def WeakThesisNotEmpiricallyEstablished (E : EpistemicFrame Claim) (w : Claim) : Prop :=
  ¬ E.empiricallyEstablished w

/-- Second-order outcome (`STMT-WEAK-SCIENTISM-DEMARCATION-OUTCOME`): inside its
own domain the weak thesis inherits horn 1; outside, if established, it
concedes a non-empirically established claim and strong scientism fails. -/
def WeakScientismDemarcationOutcome (E : EpistemicFrame Claim) (scope : Claim → Prop)
    (D : Norm.Demarcation Claim) (w : Claim) : Prop :=
  (D.inDomain w → WeakScientism E scope D → ¬ E.established w) ∧
    (¬ D.inDomain w → E.established w →
      SomeNonEmpiricalEstablished E ∧ ¬ ScopedScientism E scope)

/-- Weak scientism with its formulation outside its domain is consistent, with
the domain non-trivially occupied (`STMT-WEAK-SCIENTISM-CONSISTENT`). -/
def WeakScientismConsistent : Prop :=
  ∃ (E : EpistemicFrame Bool) (scope : Bool → Prop) (D : Norm.Demarcation Bool) (w : Bool),
    scope w ∧ ¬ E.empiricallyEstablished w ∧ ¬ D.inDomain w ∧ E.established w ∧
      WeakScientism E scope D ∧
        (∃ c, D.inDomain c ∧ E.established c ∧ E.empiricallyEstablished c)

end TruthCore.Logic.Scientism
