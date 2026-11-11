module

/-!
Analyst structural test for #1397, not a model of full Thomistic hylomorphism.
A form-token/body-token attachment relation at times has no person, substantial
esse, living organization or original-matter semantics. The numerical token
carrier is stipulated, not an account of individuation. Persistent represented
availability of a form token is NOT continuity of substantial esse.
-/
@[expose] public section
namespace TruthCore.Mereology.FormMate1397

/-- At one time, the selected form token has at most one attached body token. -/
def UniqueAt {T S B : Type} (attached : T → S → B → Prop) : Prop :=
  ∀ t s b c, attached t s b → attached t s c → b = c

/-- A stronger ALL-TIME restriction: any two admitted attachments of a form
have the same body token, even at different times. Its applicability is OPEN;
this is not derived merely by naming the form a soul. -/
def StableMate {T S B : Type} (attached : T → S → B → Prop) : Prop :=
  ∀ t u s b c, attached t s b → attached u s c → b = c

inductive Era where | before | gap | returned
  deriving DecidableEq
inductive FormToken where | designated
  deriving DecidableEq
inductive BodyToken where | original | other
  deriving DecidableEq

/-- Two attachment profiles use exactly the same form and time carriers. -/
inductive Profile where | restored | changedMate
  deriving DecidableEq

def finalBody : Profile → BodyToken
  | .restored => .original
  | .changedMate => .other

/-- A token-existence predicate, not substantial esse or a living person. -/
def formAvailable (_ : Era) (_ : FormToken) : Prop := True

/-- Endpoints have one designated attachment; the intervening time has none.
Body identities are explicit primitive labels, not particle-inventory or
organism-persistence judgments. -/
def attached (p : Profile) : Era → FormToken → BodyToken → Prop
  | .before, .designated, b => b = .original
  | .gap, .designated, _ => False
  | .returned, .designated, b => b = finalBody p

/-- Formal insufficiency of time-local exclusivity for all-time mate stability,
retaining represented token existence at every time, occupied endpoints and a
bodyless gap. Neither profile is certified possible or a complete source theory.
The restored profile satisfies the all-time restriction nonvacuously. -/
def Certificate : Prop :=
  (∀ p, UniqueAt (attached p)) ∧
  (∀ t, formAvailable t .designated) ∧
  (∀ p, attached p .before .designated .original ∧
    attached p .returned .designated (finalBody p)) ∧
  (∀ p b, ¬ attached p .gap .designated b) ∧
  ¬ StableMate (attached .changedMate) ∧
  StableMate (attached .restored) ∧
  finalBody .changedMate ≠ BodyToken.original

end TruthCore.Mereology.FormMate1397
