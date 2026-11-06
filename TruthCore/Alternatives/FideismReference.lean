module

public import TruthCore.Alternatives.Fideism

/-!
A typed reference relation for the fideism comparison (#1010; owner request
2026-11-05): what a name refers to in a religious practice's use.

The early-Phillips rival on the nominal-identification leaves is the
unattributed reconstruction `STMT-GOD-NAMES-NO-BEING-WF-P1`: in the practice's
use the name "God" applies to no being. To test it against *Dei Filius* ch. 1
and can. I.1, the practice of `TruthCore.Alternatives.Fideism` gets names,
beings and two predicates:

* `RefersTo n b`: in the practice's use, the name `n` refers to (applies to)
  the being `b` (`DEF-NAME-REFERS-IN-PRACTICE`). It is the practice-use sense
  of application. The nominal-definition leaves use a predicate `God : Being →
  Prop`, the name's application in its proper sense (`DEF-GOD-NOMINAL-Q13`);
  `DISAMB-NAME-APPLICATION` keeps the two apart, and the link theorems below
  instantiate the leaves' predicate with `RefersTo god` only as a schema.
* `ConfessesReferent m n`: the move `m` confesses, with the name `n`, that
  there is a being it names, as the confession of "unum verum Deum ...
  Creatorem et Dominum" does (`DEF-CONFESSES-REFERENT`). It is a property of
  the move, not yet a fact about reference: from a correct confession to
  reference is the grammar-fixes-reference bridge.
-/

@[expose] public section

namespace TruthCore.Alternatives.FideismReference

open TruthCore.Alternatives.Fideism

/-- A religious practice with names, beings, a typed reference relation and
referential confession (module documentation). -/
structure NamingPractice (Being : Type) extends Practice where
  Name : Type
  RefersTo : Name → Being → Prop
  ConfessesReferent : Move → Name → Prop

variable {Being : Type}

/-- The WF-P1 reconstruction (`STMT-GOD-NAMES-NO-BEING-WF-P1`), unattributed: in
the practice's use the name `god` refers to no being. Phillips's reported
remark (praise "does not refer to some object called God") only supports it. -/
def GodNamesNoBeingReading (N : NamingPractice Being) (god : N.Name) : Prop :=
  ∀ b, ¬ N.RefersTo god b

/-- The practice's rule (`STMT-DEI-FILIUS-CONFESSES-ONE-TRUE-GOD`): some defined
move confesses, with the name `god`, that there is a being it names. *Dei
Filius* can. I.1: "Si quis unum verum Deum visibilium et invisibilium
Creatorem et Dominum negaverit; anathema sit", with ch. 1's confession of one
true God, a substance "re et essentia a mundo distinctus". -/
def CouncilConfessesGodReading (N : NamingPractice Being) (god : N.Name) : Prop :=
  ∃ m, N.ConfessesReferent m god ∧ N.Defined m

/-- WF-P2's reference thesis as a bridge (`STMT-GRAMMAR-FIXES-REFERENCE`): a
correct move of the practice that confesses `god` as naming a being makes the
name refer, in the practice's use, to some being. Supported, not stated, by
late Phillips ("By all means say that 'God' functions as a referring
expression ... what speaking of 'reference' ... amounts to" must be shown in
the religious context, SEP *Religious Language* §4.1) and by PU §373. -/
def GrammarFixesReferenceReading (N : NamingPractice Being) (god : N.Name) : Prop :=
  ∀ m, N.Correct m → N.ConfessesReferent m god → ∃ b, N.RefersTo god b

/-- Conclusion (`STMT-FIDEIST-REFERENCE-BUNDLE-FAILS-FOR-CATHOLIC-PRACTICE`): the
bundle of internal grammar, grammar-fixed reference and the WF-P1
reconstruction does not hold of the practice. -/
def FideistReferenceBundleFails (N : NamingPractice Being) (god : N.Name) : Prop :=
  ¬ (InternalGrammarReading N.toPractice ∧ GrammarFixesReferenceReading N god ∧
      GodNamesNoBeingReading N god)

end TruthCore.Alternatives.FideismReference
