module
public import TruthCore.Explanation.EmptyTruthmaker

/-! Analyst-stipulated replies, not attributions to named philosophers. These
finite fragments distinguish content and eligibility from truth alone. They
model neither a general theory of grounding nor metaphysical possibility.
Absence and totality tokens are reified entities only by explicit stipulation;
their existence is not inferred from a true proposition. No causal structural
properties or metaphysical generalization are assumed. -/
@[expose] public section
namespace TruthCore.Explanation.EmptyTruthmakerReplies
open TruthCore.Explanation.PSRStrength TruthCore.Explanation.TruthmakerTheories

/-- A concrete object and nonconcrete candidates of genuinely different content.
Two rigid totality tokens encode respectively the empty and singleton inventory;
we do not let one rigid token silently change its totality content by world. -/
inductive Bearer | object | abstractObject | proposition | absence | totalEmpty | totalOne | external
  deriving DecidableEq
inductive Fact | positive | negative | tautology | emptyInventory | singletonInventory
  deriving DecidableEq

def concrete (w : Bool) (b : Bearer) : Prop := w = false ∧ b = .object

def existsAt (w : Bool) (b : Bearer) : Prop := match b with
  | .object | .totalOne | .external => w = false
  | .absence | .totalEmpty => w = true
  | .abstractObject | .proposition => True

def holds (w : Bool) (f : Fact) : Prop := match f with
  | .positive | .singletonInventory => w = false
  | .negative | .emptyInventory => w = true
  | .tautology => True

def replyArena : Arena Bool Bearer Fact where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := existsAt, Causes := fun _ _ _ => False }
  holds := holds
  exist := fun b => match b with
    | .object | .external => .positive
    | .abstractObject | .proposition => .tautology
    | .absence => .negative
    | .totalEmpty => .emptyInventory
    | .totalOne => .singletonInventory
  explains := fun _ _ _ => False
  conjunct := fun g f => g = f

/-- Primitive making restricted to a specified bearer and true negative.
The content constraints below, rather than the label, distinguish profiles. -/
def byBearer (b : Bearer) : Making Bool Bearer Fact :=
  fun w x f => w = true ∧ x = b ∧ f = .negative

def abstractMaking := byBearer .abstractObject
def absenceMaking := byBearer .absence
def totalityMaking := byBearer .totalEmpty
def externalMaking := byBearer .external

/-- Absence token has precisely negative content and is admitted exactly where
that absence obtains. This is a substantive reification/eligibility policy. -/
def AbsenceContent : Prop :=
  (∀ w, existsAt w .absence ↔ holds w .negative) ∧
  (∀ w, holds w .negative ↔ ∀ b, ¬ concrete w b)

/-- Exact concrete inventory encoded by two different rigid totality tokens.
At a populated world the singleton inventory is not the empty inventory.
Only the empty totality token is eligible to make the empty negative true. -/
def inventory (token : Bearer) (b : Bearer) : Prop :=
  token = .totalOne ∧ b = .object

def TotalityContent : Prop :=
  (∀ w, existsAt w .totalEmpty ↔ ∀ b, concrete w b ↔ inventory .totalEmpty b) ∧
  (∀ w, existsAt w .totalOne ↔ ∀ b, concrete w b ↔ inventory .totalOne b) ∧
  (∀ b, ¬ inventory .totalEmpty b) ∧ inventory .totalOne .object

/-- The external candidate ACTUALLY exists at another accessible world while
absent at the target. This does not satisfy world immanence, even though it is
not absent everywhere. It does not explain how external grounding works. -/
def ExistingExternal : Prop :=
  existsAt false .external ∧ ¬ existsAt true .external ∧
  replyArena.ontic.frame.access true false ∧ externalMaking true .external .negative

/-- Reified proposition control on the existing wholly concrete-empty arena.
Both eligibility and its making relation are additional commitments; a bare
necessary truth supplies neither. Here the negative itself is necessary, unlike
the contingent absence in replyArena. This scope change is explicit. -/
def necessaryArena : Arena Bool Unit Fact where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True, Causes := fun _ _ _ => False }
  holds := fun _ _ => True
  exist := fun _ => .tautology
  explains := fun _ _ _ => False
  conjunct := fun g f => g = f

/-- Content assigned to the reified proposition token; its eligibility and
primitive making remain independently stipulated. -/
def propositionContent (_ : Unit) (_ : Bool) : Prop := True

def necessaryMaking : Making Bool Unit Fact := fun _ _ f => f = .negative

/-- Content entailment must not be confused with primitive making. A necessarily
true content cannot entail the contingent negative in the two-world profile. -/
def ContentEntailsNegative (content : Bool → Prop) : Prop :=
  ∀ w, content w → holds w .negative

def RepliesMap : Prop :=
  ConcreteEmptyFact replyArena concrete .negative ∧
  (∀ w b, concrete w b → existsAt w b) ∧
  (TruthSound replyArena abstractMaking ∧ WorldImmanent replyArena abstractMaking ∧
    NeedsMakerAt replyArena abstractMaking true .negative ∧
    ¬ ConcreteMaker abstractMaking concrete ∧
    ¬ MakerNecessitation replyArena abstractMaking) ∧
  (AbsenceContent ∧ TruthSound replyArena absenceMaking ∧
    WorldImmanent replyArena absenceMaking ∧
    NeedsMakerAt replyArena absenceMaking true .negative ∧
    ¬ ConcreteMaker absenceMaking concrete ∧
    MakerNecessitation replyArena absenceMaking) ∧
  (TotalityContent ∧ TruthSound replyArena totalityMaking ∧
    WorldImmanent replyArena totalityMaking ∧
    NeedsMakerAt replyArena totalityMaking true .negative ∧
    ¬ ConcreteMaker totalityMaking concrete ∧
    MakerNecessitation replyArena totalityMaking) ∧
  (ExistingExternal ∧ TruthSound replyArena externalMaking ∧
    NeedsMakerAt replyArena externalMaking true .negative ∧
    ¬ WorldImmanent replyArena externalMaking ∧
    ¬ ConcreteMaker externalMaking concrete ∧
    ¬ MakerNecessitation replyArena externalMaking) ∧
  (ConcreteEmptyFact necessaryArena (fun _ _ => False) .negative ∧
    TruthSound necessaryArena necessaryMaking ∧
    WorldImmanent necessaryArena necessaryMaking ∧
    MakerNecessitation necessaryArena necessaryMaking ∧
    (∀ w, NeedsMakerAt necessaryArena necessaryMaking w .negative) ∧
    (∀ w, necessaryArena.holds w .negative) ∧
    (∀ w, necessaryArena.ontic.ExistsAt w ()) ∧
    (∀ w, propositionContent () w ↔ necessaryArena.holds w .negative) ∧
    ¬ ConcreteMaker necessaryMaking (fun _ _ => False) ∧
    ¬ NeedsMakerAt necessaryArena noMaking true .negative) ∧
  ¬ ContentEntailsNegative (fun _ => True)
end TruthCore.Explanation.EmptyTruthmakerReplies
