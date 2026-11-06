module

public import TruthCore.Causality.EsseReception
public import TruthCore.Results.Aquinas.SummaTheologiae.SubsistentInfinityFromReception.Solution
public import TruthCore.Logic.ExcludedMiddle

/-! Analyst reconstruction of the existing united-soul/body reception objection.
State, human subject, soul bearer, receiving corporeal principle and communicated
act are separate typed data. No source communication is identified with the old
EsseReceivedIn relation without an explicit same-act interpretation transfer.
Actual union, conditional communication, act identity, and recipient distinctness
from the soul's essence are independent premises. The selected whole's essence
is never silently substituted for the soul's essence.
-/

@[expose] public section
namespace TruthCore.Causality.EsseReceptionDefinitionFork
open TruthCore.Causality.EsseReception

structure Frame where
  Being : Type
  Principle : Type
  State : Type
  selected : State
  human : Being
  soulOf : Being → Being
  bodyOf : Being → Principle
  essenceOf : Being → Principle
  esseOf : Being → Principle
  communicatedAct : Principle
  Unites : State → Being → Being → Principle → Prop
  Communicates : State → Being → Principle → Principle → Prop
  Received : State → Being → Principle → Prop
  Eligible : State → Being → Prop

/-- Actual selected union; `human`, its soul bearer and its bodily recipient
are distinct roles, not assumed distinct inhabitants of one carrier. -/
def SelectedUnion (f : Frame) : Prop :=
  f.Unites f.selected f.human (f.soulOf f.human) (f.bodyOf f.human)

def UnitedCommunication (f : Frame) : Prop :=
  SelectedUnion f →
    f.Communicates f.selected (f.soulOf f.human) f.communicatedAct (f.bodyOf f.human)

def CommunicatedActIsSoulEsse (f : Frame) : Prop :=
  f.communicatedAct = f.esseOf (f.soulOf f.human)

/-- Open interpretive bridge, not a definition of communication: communication
of that very soul's esse to the same bodily recipient counts as the canonical
reception relation in the same state. It need not hold for every sense of
communication or every recipient mentioned by an unrelated description. -/
def SameSenseTransfer (f : Frame) : Prop :=
  ∀ s h e, f.Unites s h (f.soulOf h) (f.bodyOf h) →
    f.Communicates s (f.soulOf h) e (f.bodyOf h) →
    e = f.esseOf (f.soulOf h) → f.Received s (f.soulOf h) (f.bodyOf h)

def FurtherInterpretation (f : Frame) : Prop :=
  ∃ s h e, f.Unites s h (f.soulOf h) (f.bodyOf h) ∧
    f.Communicates s (f.soulOf h) e (f.bodyOf h) ∧
    e = f.esseOf (f.soulOf h) ∧ ¬ f.Received s (f.soulOf h) (f.bodyOf h)

def SameSenseTransferFails (f : Frame) : Prop := ¬ SameSenseTransfer f

def TransferFork : Prop := ∀ f, SameSenseTransfer f ∨ FurtherInterpretation f

def SelectedReception (f : Frame) : Prop :=
  f.Received f.selected (f.soulOf f.human) (f.bodyOf f.human)

def SelectedNonReception (f : Frame) : Prop := ¬ SelectedReception f

def SelectedFork : Prop := ∀ f, SelectedReception f ∨ SelectedNonReception f

def BodyIsNotSoulEssence (f : Frame) : Prop :=
  f.bodyOf f.human ≠ f.essenceOf (f.soulOf f.human)

def OwnEssenceFails (f : Frame) : Prop :=
  ¬ EsseReceivedOnlyInOwnEssence f.essenceOf (f.Received f.selected)

/-- Scope-restricted sibling, whose eligibility criterion must be supplied.
No source claim identifies Eligible with separated souls, all subsistent forms,
or any other domain. Excluding this case is an additional scope commitment. -/
def RestrictedOwnEssence (f : Frame) : Prop :=
  ∀ x r, f.Eligible f.selected x → f.Received f.selected x r → r = f.essenceOf x

def SelectedSoulEligible (f : Frame) : Prop :=
  f.Eligible f.selected (f.soulOf f.human)

def RestrictedOwnEssenceFails (f : Frame) : Prop := ¬ RestrictedOwnEssence f

/-- Same shared fixture: the selected human is true, its soul bearer false,
recipient true and own essence false. These are role labels only. -/
def sameSense : Frame where
  Being := Bool
  Principle := Bool
  State := Unit
  selected := ()
  human := true
  soulOf := fun _ => false
  bodyOf := fun _ => true
  essenceOf := fun _ => false
  esseOf := fun _ => false
  communicatedAct := false
  Unites := fun _ _ _ _ => True
  Communicates := fun _ _ e _ => e = false
  Received := fun _ _ r => r = true
  Eligible := fun _ _ => False

def differentSense : Frame := { sameSense with Received := fun _ _ _ => False }

def wrongAct : Frame :=
  { differentSense with
    communicatedAct := true
    Communicates := fun _ _ e _ => e = true }

def noUnion : Frame := { differentSense with Unites := fun _ _ _ _ => False }
def noCommunication : Frame := { differentSense with Communicates := fun _ _ _ _ => False }
def sameEssence : Frame := { sameSense with essenceOf := fun _ => true }

/-- Exact named finite boundaries; no actual anthropology or metaphysical
possibility is inferred. -/
def Controls : Prop :=
  (SelectedUnion sameSense ∧ UnitedCommunication sameSense ∧
    CommunicatedActIsSoulEsse sameSense ∧ SameSenseTransfer sameSense ∧
    BodyIsNotSoulEssence sameSense ∧ SelectedReception sameSense ∧
    OwnEssenceFails sameSense ∧ RestrictedOwnEssence sameSense) ∧
  (SelectedUnion differentSense ∧ UnitedCommunication differentSense ∧
    CommunicatedActIsSoulEsse differentSense ∧ BodyIsNotSoulEssence differentSense ∧
    SelectedNonReception differentSense ∧ FurtherInterpretation differentSense ∧
    EsseReceivedOnlyInOwnEssence differentSense.essenceOf (differentSense.Received differentSense.selected)) ∧
  (SelectedUnion wrongAct ∧ UnitedCommunication wrongAct ∧ SameSenseTransfer wrongAct ∧
    ¬ CommunicatedActIsSoulEsse wrongAct ∧ SelectedNonReception wrongAct) ∧
  (UnitedCommunication noUnion ∧ CommunicatedActIsSoulEsse noUnion ∧ SameSenseTransfer noUnion ∧
    ¬ SelectedUnion noUnion ∧ SelectedNonReception noUnion) ∧
  (SelectedUnion noCommunication ∧ CommunicatedActIsSoulEsse noCommunication ∧
    SameSenseTransfer noCommunication ∧ ¬ UnitedCommunication noCommunication ∧
    SelectedNonReception noCommunication) ∧
  (SelectedReception sameEssence ∧
    EsseReceivedOnlyInOwnEssence sameEssence.essenceOf (sameEssence.Received sameEssence.selected) ∧
    ¬ BodyIsNotSoulEssence sameEssence)


/-- Weakest own-essence scope used by the old infinity proof: only beings whose
represented esse already is their essence. This does not assert that such a
being exists or that a united soul belongs to that class. -/
def IdentityScopedOwnEssence (f : Frame) : Prop :=
  ∀ x r, f.esseOf x = f.essenceOf x →
    f.Received f.selected x r → r = f.essenceOf x

/-- Explicit proof-irrelevant bounds avoid the OfNat Fin convenience instance's
propext dependency; the fixed Fin3 values remain exactly0,1,2. -/
def role0 : Fin 3 := ⟨0, Nat.zero_lt_succ 2⟩
def role1 : Fin 3 := ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 1)⟩
def role2 : Fin 3 := ⟨2, Nat.lt_succ_self 2⟩

/-- A separate profile frozen for scope strictness: nonidentity soul bearer
false, identity candidate true, bodily recipient2, communicated act0. The whole
human and soul roles are distinct here; neither is identified with a receiver. -/
def identityScopeControl : Frame where
  Being := Bool
  Principle := Fin 3
  State := Unit
  selected := ()
  human := true
  soulOf := fun _ => false
  bodyOf := fun _ => role2
  essenceOf := fun x => if x then role0 else role1
  esseOf := fun _ => role0
  communicatedAct := role0
  Unites := fun _ _ _ _ => True
  Communicates := fun _ _ e _ => e = role0
  Received := fun _ x r => x = false ∧ r = role2
  Eligible := fun _ _ => False

def IdentityScopeControl : Prop :=
  SelectedUnion identityScopeControl ∧ UnitedCommunication identityScopeControl ∧
  CommunicatedActIsSoulEsse identityScopeControl ∧ SameSenseTransfer identityScopeControl ∧
  BodyIsNotSoulEssence identityScopeControl ∧ SelectedReception identityScopeControl ∧
  OwnEssenceFails identityScopeControl ∧ IdentityScopedOwnEssence identityScopeControl ∧
  (∃ x, identityScopeControl.esseOf x = identityScopeControl.essenceOf x)

end TruthCore.Causality.EsseReceptionDefinitionFork
