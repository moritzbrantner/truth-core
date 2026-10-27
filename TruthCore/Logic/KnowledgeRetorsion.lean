/-!
A source-free Cartesian-style test of a universal denial of knowledge (#515).
Knowledge is factive in this explicit profile: knowing p implies p. This is
not inferred from a speaker's assertion. The universal denial is itself one
of the propositions over which it quantifies.

The result excludes knowledge of universal ignorance under factivity, not
universal ignorance itself, nonassertive scepticism, or lack of justification.
The controls separate assertion from knowledge and expose the factivity cost.
No actual knower, empirical episode, or external world is inferred.
-/

namespace TruthCore.Logic.KnowledgeRetorsion

universe u

/-- Factive knowledge: whoever knows a proposition knows something true.
No instance of knowledge is asserted to exist. -/
def FactiveKnowledge {Agent : Type u} (Knows : Agent → Prop → Prop) : Prop :=
  ∀ a p, Knows a p → p

/-- Universal ignorance: no agent knows any proposition, including this denial.
Mere assertion is not knowledge. -/
def UniversalNoKnowledge {Agent : Type u} (Knows : Agent → Prop → Prop) : Prop :=
  ∀ a p, ¬ Knows a p

/-- Under factivity nobody knows the universal denial of all knowledge.
The condition is explicit; this is not an existence theorem for knowledge. -/
def NoFactiveKnowerOfUniversalNoKnowledge : Prop :=
  ∀ (Agent : Type u) (Knows : Agent → Prop → Prop),
    FactiveKnowledge Knows → ∀ a, ¬ Knows a (UniversalNoKnowledge Knows)

/-- An agent can assert the denial while no one knows anything. -/
def AssertedNoKnowledgeModel : Prop :=
  ∃ (Knows Asserts : Unit → Prop → Prop),
    FactiveKnowledge Knows ∧ UniversalNoKnowledge Knows ∧
      Asserts () (UniversalNoKnowledge Knows)

/-- Without factivity an apparent knower of the denial is possible. -/
def NonfactiveKnownNoKnowledgeModel : Prop :=
  ∃ (Knows : Unit → Prop → Prop),
    Knows () (UniversalNoKnowledge Knows) ∧ ¬ FactiveKnowledge Knows

end TruthCore.Logic.KnowledgeRetorsion
