module

public import TruthCore.Case.Catholicism.StageTwo
public import TruthCore.Latin.Aquinas.SummaTheologiae.PrimaPars.Question3.Article1

/-! Finite interpretations of the unchanged four-premise immutability argument.
Bool beings distinguish the designated god (true) from a mutable being (false).
Bool respects distinguish esse (false) from a further perfection (true).
These are logical interpretations, not claims of metaphysical possibility. -/

@[expose] public section
namespace TruthCore.Case.Catholicism.RootBundleWitnessImmutable
open TruthCore.Latin.Aquinas.SummaTheologiae

structure Interpretation where
  god : Bool → Prop
  act : Bool → Bool → Prop
  potency : Bool → Bool → Prop
  more : Bool → Bool → Bool → Prop
  prior : Bool → Bool → Prop

def Maximal (m : Interpretation) : Prop :=
  GodIsMaximalInBeing m.god m.act m.more false
def First (m : Interpretation) : Prop :=
  MaximumInBeingIsFirstBeing m.act m.more false m.prior
def Priority (m : Interpretation) : Prop :=
  ActSimplyPriorToPotencyReading m.act m.potency m.prior
def Nonoverlap (m : Interpretation) : Prop :=
  NotActAndPotencyInSameRespectReading m.act m.potency
def Conclusion (m : Interpretation) : Prop :=
  GodIsImmutable m.god (IsImmutable m.potency)
def Joint (m : Interpretation) : Prop :=
  Maximal m ∧ First m ∧ Priority m ∧ Nonoverlap m

def positive : Interpretation where
  god x := x = true
  act x r := x = true ∨ r = false
  potency x r := x = false ∧ r = true
  more _ x y := x = true ∧ y = false
  prior x y := x = true ∧ y = false

-- Each omission keeps all vocabulary definitions fixed and changes only
-- the supplied interpretation. The negated conclusion has an actual god.
def withoutMaximal : Interpretation :=
  { positive with god := fun x => x = false }
def withoutFirst : Interpretation :=
  { positive with
    act := fun x r => r = false ∨ x = false
    potency := fun x r => x = true ∧ r = true
    prior := fun x y => x = false ∧ y = true }
def withoutPriority : Interpretation :=
  { withoutFirst with prior := positive.prior }
def withoutNonoverlap : Interpretation :=
  { positive with
    potency := fun x r => x = true ∧ r = true
    prior := fun x y => x = true ∧ (y = false ∨ y = true) }

/-- All four premises together, a god, a distinct mutable being, and an actual
priority edge. In particular the priority premise is exercised by real potency. -/
def PositiveCertificate : Prop :=
  Joint positive ∧ Conclusion positive ∧ positive.god true ∧
  positive.potency false true ∧ positive.act true true ∧
  positive.prior true false ∧ ¬ positive.act false true

def OmissionCertificate : Prop :=
  (¬ Maximal withoutMaximal ∧ First withoutMaximal ∧ Priority withoutMaximal ∧
    Nonoverlap withoutMaximal ∧ ¬ Conclusion withoutMaximal) ∧
  (Maximal withoutFirst ∧ ¬ First withoutFirst ∧ Priority withoutFirst ∧
    Nonoverlap withoutFirst ∧ ¬ Conclusion withoutFirst) ∧
  (Maximal withoutPriority ∧ First withoutPriority ∧ ¬ Priority withoutPriority ∧
    Nonoverlap withoutPriority ∧ ¬ Conclusion withoutPriority) ∧
  (Maximal withoutNonoverlap ∧ First withoutNonoverlap ∧ Priority withoutNonoverlap ∧
    ¬ Nonoverlap withoutNonoverlap ∧ ¬ Conclusion withoutNonoverlap)

/-- Exact finite certificate, including the specified positive and negative
facts. No independent applicability of any predicate is asserted. -/
def Certificate : Prop := PositiveCertificate ∧ OmissionCertificate
def immutable : Bool → Prop := IsImmutable positive.potency
end TruthCore.Case.Catholicism.RootBundleWitnessImmutable
