module

public import TruthCore.Alternatives.Fideism

/-!
Analyst interpretations of internal natural reason, with attribution deferred.
Scope is supplied, never inferred from a theological audience. Sufficiency is
one-way; determination adds the converse. Neither defines normative authority.
Authority is an explicitly primitive jurisdiction relation: a standard may judge
correctness, whether or not it endorses a move or agrees with another standard.
No law identifies jurisdiction with actual correctness or shared agreement.
The original mixed horizon sense remains unbound pending a mapping/coverage case.
-/

@[expose] public section

namespace TruthCore.Alternatives.NaturalReasonAuthority
open TruthCore.Alternatives.Fideism

/-- Weak internal sufficiency on exactly the supplied moves. This is a logical
condition, not a causal or exclusive explanation of correctness. -/
def InternalSufficiency (P : Practice) (scope : P.Move → Prop) : Prop :=
  ∀ m, scope m → P.OwnStandard m → P.Correct m

/-- Stronger extensional determination on the same scope, not exclusive
normative jurisdiction. The reverse implication is an additional commitment. -/
def InternalDetermination (P : Practice) (scope : P.Move → Prop) : Prop :=
  ∀ m, scope m → (P.OwnStandard m ↔ P.Correct m)

/-- Primitive standards and their jurisdiction over correctness. Internal means
belonging to this practice; HasAuthority means entitled to judge this move,
not actual endorsement, correctness, or agreement. All instances remain open. -/
structure AuthorityProfile (P : Practice) where
  Standard : Type
  Internal : Standard → Prop
  HasAuthority : Standard → P.Move → Prop

/-- No standard outside this practice has jurisdiction over scoped moves.
This adds no positive endorsement or correctness condition. -/
def ExternalAuthorityExcluded (P : Practice) (A : AuthorityProfile P)
    (scope : P.Move → Prop) : Prop :=
  ∀ s m, scope m → ¬ A.Internal s → ¬ A.HasAuthority s m

/-- Controls export four inhabited combinations of sharedness and external
jurisdiction while retaining internal determination; strictness of one-way
sufficiency and of natural versus all-move scope; and exclusion with failed
sufficiency. They are formal dictionaries, not actual religious practices. -/
def ForkControls : Prop :=
  (∀ shared external : Bool, ∃ P : Practice, ∃ A : AuthorityProfile P, ∃ m,
    P.AffirmsNaturalKnowability m ∧ P.OwnStandard m ∧ P.Correct m ∧
    InternalDetermination P P.AffirmsNaturalKnowability ∧
    (P.AnswersToSharedReason m ↔ shared = true) ∧
    (ExternalAuthorityExcluded P A P.AffirmsNaturalKnowability ↔ external = false)) ∧
  (∃ P : Practice, ∃ m, P.AffirmsNaturalKnowability m ∧
    InternalSufficiency P P.AffirmsNaturalKnowability ∧
    ¬ InternalDetermination P P.AffirmsNaturalKnowability) ∧
  (∃ P : Practice, ∃ m, P.AffirmsNaturalKnowability m ∧
    InternalSufficiency P P.AffirmsNaturalKnowability ∧
    ¬ InternalSufficiency P (fun _ => True)) ∧
  (∃ P : Practice, ∃ A : AuthorityProfile P, ∃ m,
    P.AffirmsNaturalKnowability m ∧ P.OwnStandard m ∧ ¬ P.Correct m ∧
    ExternalAuthorityExcluded P A P.AffirmsNaturalKnowability ∧
    ¬ InternalSufficiency P P.AffirmsNaturalKnowability) ∧
  (∀ (P : Practice) (broad narrow : P.Move → Prop),
    (∀ m, narrow m → broad m) →
    (InternalSufficiency P broad → InternalSufficiency P narrow) ∧
    (InternalDetermination P broad → InternalDetermination P narrow) ∧
    (∀ A, ExternalAuthorityExcluded P A broad → ExternalAuthorityExcluded P A narrow))

end TruthCore.Alternatives.NaturalReasonAuthority
