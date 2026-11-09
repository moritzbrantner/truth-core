module

/-! Analyst declarations for the actual-knowledge scopes in CC100 item 124.
Contents and agents range over arbitrary types, without a finiteness assumption.
Truth and knowledge are explicit primitive interpretations. Their applicability,
factivity, closure, and relation to possible knowledge remain open. -/
@[expose] public section
namespace TruthCore.Logic.CommonKnowerScopes

/-- Literal step2: every content has an actual knower, including contents not
selected by a truth predicate. This does not assert factivity. -/
def EveryPropositionKnown {Content : Type u} {Agent : Type v}
    (knows : Agent → Content → Prop) : Prop :=
  ∀ p, ∃ a, knows a p

/-- Contextual step2: each actual truth has some actual knower. The witness may
vary with the content. This is not a common-knower assertion. -/
def EveryTruthKnown {Content : Type u} {Agent : Type v}
    (isTrue : Content → Prop) (knows : Agent → Content → Prop) : Prop :=
  ∀ p, isTrue p → ∃ a, knows a p

/-- The distinct common-knower consequent of step3. No implication to this
formula from either per-content scope is built into the definitions. -/
def CommonTruthKnower {Content : Type u} {Agent : Type v}
    (isTrue : Content → Prop) (knows : Agent → Content → Prop) : Prop :=
  ∃ a, ∀ p, isTrue p → knows a p

/-- Finite control only: even unguarded per-content knowledge and factivity do
not exchange the existential witnesses for one common knower. This does not
model the intended domain of all propositions. -/
theorem noWitnessExchange :
    EveryPropositionKnown (fun (a p : Bool) => a = p) ∧
    EveryTruthKnown (fun (_ : Bool) => True) (fun a p => a = p) ∧
    ¬ CommonTruthKnower (fun (_ : Bool) => True) (fun a p => a = p) := by
  refine ⟨fun p => ⟨p, rfl⟩, fun p _ => ⟨p, rfl⟩, ?_⟩
  rintro ⟨a, h⟩
  have ht := h true trivial
  have hf := h false trivial
  exact Bool.noConfusion (ht.symm.trans hf)

/-- Finite control only: contextual knowledge allows an unknown false content;
it neither asserts all contents true nor implies literal unguarded knowledge. -/
theorem truthGuardMatters :
    EveryTruthKnown (fun p : Bool => p = true) (fun (_ : Unit) p => p = true) ∧
    ¬ EveryPropositionKnown (fun (_ : Unit) (p : Bool) => p = true) := by
  refine ⟨fun _ hp => ⟨(), hp⟩, ?_⟩
  rintro h
  obtain ⟨_, hf⟩ := h false
  exact Bool.noConfusion hf

end TruthCore.Logic.CommonKnowerScopes
