module

public import TruthCore.Alternatives.FideismReference
public import TruthCore.Case.Catholicism.StageOneQuartaVia
public import TruthCore.Case.Catholicism.Root
public import TruthCore.Logic.ExcludedMiddle

/-!
# Proper application and practice reference

The existing nominal God predicate and a naming practice's RefersTo relation
are not identified. These analyst calibration propositions say exactly what a
comparison requires on their shared Being carrier. A description may properly
apply to a person whom one community fails to name, while a name in a practice
may also refer incorrectly to someone outside its proper criterion. These are
ordinary analogies, not verdicts about the actual use of the name God.

Coextension is stronger than preserving proper application. The argument needs
only preservation, and needs an actual proper instance for global conflict
with no-reference. No translation, historical identity or philosophical theory
of reference is supplied. Applicability of each calibration remains open.
-/

@[expose] public section

namespace TruthCore.Alternatives.NameApplicationTransfer

open TruthCore.Alternatives.FideismReference
open TruthCore.Case.Catholicism
open TruthCore.Latin.Aquinas.SummaTheologiae

/-- Weak one-way calibration, on every instance of the selected proper sense. -/
def ProperReferencePreserved {Being : Type} (N : NamingPractice Being)
    (god : N.Name) (proper : Being → Prop) : Prop :=
  ∀ b, proper b → N.RefersTo god b

/-- Strong sibling: the two selected extensions coincide in both directions. -/
def SharedReferenceExtension {Being : Type} (N : NamingPractice Being)
    (god : N.Name) (proper : Being → Prop) : Prop :=
  ∀ b, proper b ↔ N.RefersTo god b

/-- A precise relevant failure, not a new spelling: a proper instance is lost
by practice reference on this shared carrier and selected name. -/
def ProperReferenceLost {Being : Type} (N : NamingPractice Being)
    (god : N.Name) (proper : Being → Prop) : Prop :=
  ∃ b, proper b ∧ ¬ N.RefersTo god b

/-- Structural coverage of the transfer test, not exhaustion of philosophical
accounts of reference. EM supplies the counterexample witness when needed. -/
def TransferCasesCover {Being : Type} (N : NamingPractice Being)
    (god : N.Name) (proper : Being → Prop) : Prop :=
  ProperReferencePreserved N god proper ∨ ProperReferenceLost N god proper

/-- WF-P1's practice-use no-reference thesis fails; proper application has not
been silently substituted for practice reference in this negation. -/
def NoBeingRejected {Being : Type} (N : NamingPractice Being) (god : N.Name) : Prop :=
  ¬ GodNamesNoBeingReading N god

/-- Exact surviving-descriptor consequence: the full proper-naming leaf,
no-reference and transfer exclude a unique full-description witness. -/
def FullDescriptionExcluded {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) : Prop :=
  ∀ m, IsMaximumIn InAct MoreIn esse m → CausesAllInGenus InAct CausesIn esse m →
    CausesEveryPerfectionOfOthers InAct CausesIn m → RemoteFromAll ComponentOf m →
    ¬ (∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m)

/-- A witness satisfying every antecedent of the full naming leaf. -/
def FullDescriptorExists {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) : Prop :=
  ∃ m, IsMaximumIn InAct MoreIn esse m ∧ CausesAllInGenus InAct CausesIn esse m ∧
    CausesEveryPerfectionOfOthers InAct CausesIn m ∧ RemoteFromAll ComponentOf m ∧
    (∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m)

/-- A witness satisfying the reduced naming leaf's antecedents. -/
def ReducedDescriptorExists {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect) : Prop :=
  ∃ m, IsMaximumIn InAct MoreIn esse m ∧ CausesAllInGenus InAct CausesIn esse m ∧
    (∀ m', IsMaximumIn InAct MoreIn esse m' → m' = m)

/-- A witness satisfying the first-mover naming leaf's antecedents. -/
def PureActDescriptorExists {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (PureAct : Being → Prop) : Prop :=
  ∃ f, IsFirstUnmovedMover MovedIn MovesIn f ∧ PureAct f ∧
    (∀ g, IsFirstUnmovedMover MovedIn MovesIn g → g = f)

/-- Actual negation of the proper-sense full naming proposition. -/
def FullNominalNamingFails {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (ComponentOf : Being → Being → Prop) (proper : Being → Prop) : Prop :=
  ¬ GodNamesTheFullyDescribedPrinciple InAct MoreIn CausesIn esse ComponentOf proper

/-- Actual negation of the proper-sense reduced naming proposition. -/
def ReducedNominalNamingFails {Being Respect : Type}
    (InAct : Being → Respect → Prop) (MoreIn : Respect → Being → Being → Prop)
    (CausesIn : Being → Being → Respect → Prop) (esse : Respect)
    (proper : Being → Prop) : Prop :=
  ¬ GodNamesTheUniqueMaximeEns InAct MoreIn CausesIn esse proper

/-- Actual negation of the proper-sense first-mover naming proposition. -/
def PureActNominalNamingFails {Being Respect : Type}
    (MovedIn : Being → Respect → Prop) (MovesIn : Being → Being → Respect → Prop)
    (PureAct proper : Being → Prop) : Prop :=
  ¬ UniquePureActFirstMoverIsGod MovedIn MovesIn PureAct proper

/-- Three finite controls: a proper inhabitant survives no-reference without
transfer; joint reference with a proper inhabitant defeats no-reference; and
one-way preservation can hold without coextension. These are schema controls. -/
def TransferModels : Prop :=
  (∃ N : NamingPractice Unit, ∃ god : N.Name, ∃ proper : Unit → Prop,
    GodExists proper ∧ GodNamesNoBeingReading N god ∧ ProperReferenceLost N god proper ∧
    ¬ ProperReferencePreserved N god proper) ∧
  (∃ N : NamingPractice Unit, ∃ god : N.Name, ∃ proper : Unit → Prop,
    GodExists proper ∧ SharedReferenceExtension N god proper ∧
    ProperReferencePreserved N god proper ∧ NoBeingRejected N god) ∧
  (∃ N : NamingPractice Bool, ∃ god : N.Name, ∃ proper : Bool → Prop,
    GodExists proper ∧ ProperReferencePreserved N god proper ∧
    ¬ SharedReferenceExtension N god proper)

end TruthCore.Alternatives.NameApplicationTransfer
