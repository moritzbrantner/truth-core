module

@[expose] public section

/-!
Non-contradiction for the case predicates: floor item F1 (#1007).

The case states its premises with predicates of beings in respects
(`InAct x r`, `InPotency x r`, `MovedIn x r`, ...). F1 says of every such
predicate that nothing both has it and lacks it in the same respect:
Aristotle, *Metaphysics* IV.3, 1005b19-20, "the same attribute cannot at the
same time belong and not belong to the same subject in the same respect".

Lean proves this outright and without axioms, so inside the encoded logic it is
no assumption. What the owner-approved floor marking on `STMT-CASE-NON-CONTRADICTION`
adds is the explicit relativity that D-L asks for (#1007): a dialetheist (Hegel
on motion, Priest) rejects that Lean's negation captures their position, so a
classical refutation of a dialetheic rival counts only relative to this
marking, as the floor marking does for excluded middle.
-/

namespace TruthCore.Logic.CaseNonContradiction

universe u v

/-- F1: for every predicate of beings in respects, nothing has it and lacks it
in the same respect. -/
def CasePredicateNonContradiction : Prop :=
  ∀ (Being : Sort u) (Respect : Sort v) (P : Being → Respect → Prop) (x : Being) (r : Respect),
    ¬ (P x r ∧ ¬ P x r)

/-- The dialetheic rival, as far as Lean's classical signature can state it:
some being both has and lacks some predicate in the same respect (Hegel,
*Wissenschaft der Logik* II, "Der Widerspruch", Anm. 3: something moves only by
being here and not here in one and the same now; Priest's dialetheic account
of motion). A dialetheist reads the second conjunct with a paraconsistent
negation, which this encoding does not represent; that is why its refutation
counts only relative to the F1 floor marking (D-L). -/
def SomeCasePredicateContradictionTrue : Prop :=
  ∃ (Being : Sort u) (Respect : Sort v) (P : Being → Respect → Prop) (x : Being) (r : Respect),
    P x r ∧ ¬ P x r

/-- The dialetheic rival fails: no being both has and lacks a case predicate in
the same respect. Lean proves it without axioms; against a dialetheist it
counts only relative to the F1 floor marking (D-L). -/
def NoCasePredicateContradiction : Prop :=
  ¬ SomeCasePredicateContradictionTrue.{u, v}

end TruthCore.Logic.CaseNonContradiction
