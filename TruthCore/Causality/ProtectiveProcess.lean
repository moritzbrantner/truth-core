module
public import TruthCore.Causality.PreservationCandidates

/-! Analyst transition semantics for indirect protection, not a completion of
q104's sourced meaning. Processes have arbitrary state carriers and may traverse
multiple edges. An intervention suppresses process edges, rather than deleting
labels. Survival additionally needs explicit loss coverage and no bypass.
Nothing supplies an efficient cause of esse or a timeless action. -/
@[expose] public section
namespace TruthCore.Causality.ProtectiveProcess
open PreservationCandidates

/-- Framework primitives: occurrence is an actual process edge in a history;
terminal marks its destructive endpoint. Both need an application-specific
interpretation. Threat identity supplies source and the same numerical target.
No transitivity, temporal density, modal power or well-foundedness is assumed. -/
structure Model (Being Process State : Type) where
  threat : Process → Threat Being
  occurs : Process → State → State → Prop
  terminal : Process → State → Prop
  existsAt : State → Being → Prop

/-- A terminal occurrence directed to this very bearer, not a threat label. -/
def Destroys {B P S : Type} (m : Model B P S) (p : P) (s t : S) (b : B) : Prop :=
  m.occurs p s t ∧ m.terminal p t ∧ (m.threat p).target = b

/-- Intervention semantics: on every admitted transition, blocked processes
cannot occur. Merely removing a represented threat imposes no such condition.
This is a stipulated restriction of histories, not a physical realization proof. -/
def Admissible {B P S : Type} (m : Model B P S) (blocked : P → Prop)
    (h : Nat → S) (bound : Nat) : Prop :=
  ∀ n, n < bound → ∀ p, blocked p → ¬ m.occurs p (h n) (h (n+1))

/-- Exhaustiveness is explicit: an existing bearer either persists over a step,
or some represented process has a terminal occurrence against it. This rules
out unrepresented losses, but supplies no productive cause of persistence. -/
def LossCovered {B P S : Type} (m : Model B P S) (h : Nat → S)
    (bound : Nat) (b : B) : Prop :=
  ∀ n, n < bound → m.existsAt (h n) b →
    m.existsAt (h (n+1)) b ∨ ∃ p, Destroys m p (h n) (h (n+1)) b

/-- Every terminal occurrence against this bearer on this history is blocked.
This is scoped to the supplied history/interval; other histories remain open.
Replacement processes and alternative paths are quantified, not excluded by name. -/
def NoBypass {B P S : Type} (m : Model B P S) (blocked : P → Prop)
    (h : Nat → S) (bound : Nat) (b : B) : Prop :=
  ∀ n, n < bound → ∀ p, Destroys m p (h n) (h (n+1)) b → blocked p

/-- The same bearer is present at every sampled point, including both endpoints. -/
def ProtectedInterval {B P S : Type} (m : Model B P S) (h : Nat → S)
    (bound : Nat) (b : B) : Prop := ∀ n, n ≤ bound → m.existsAt (h n) b

/-- Shared starting state plus an actual baseline edge absent after intervention.
This supplies a contrast of histories; counterfactual contrast alone is not
productive causation or an assertion that the action realizes the restriction. -/
def Interrupted {B P S : Type} (m : Model B P S) (p : P)
    (before after : Nat → S) (n : Nat) : Prop :=
  before 0 = after 0 ∧ m.occurs p (before n) (before (n+1)) ∧
    ¬ m.occurs p (after n) (after (n+1))

/-- The theorem keeps all three non-logical conditions explicit inside the
quantified conditional; none is independently established. -/
def Safety : Prop := ∀ (B P S : Type) (m : Model B P S) (blocked : P → Prop)
    (h : Nat → S) (bound : Nat) (b : B),
  m.existsAt (h 0) b → Admissible m blocked h bound →
  LossCovered m h bound b → NoBypass m blocked h bound b →
  ProtectedInterval m h bound b

/-- Action-to-transition interface: the existing action addresses its own threat,
and every process carrying that threat is suppressed. This is an explicit OPEN
realization premise. Its body constrains transitions, not a success flag. -/
def RealizesInterception {B P S : Type} (m : Model B P S) (a : Action B)
    (h : Nat → S) (bound : Nat) : Prop :=
  ∃ threat, a.contribution = .intercepting threat ∧ threat.target = a.bearer ∧
    a.ongoing ∧ Admissible m (fun p => m.threat p = threat) h bound

def ActionProjection : Prop := ∀ (B P S : Type) (m : Model B P S)
    (a : Action B) (h : Nat → S) (bound : Nat),
  RealizesInterception m a h bound → InterceptionCandidate a

inductive Stage where | ready | burning | safe | lost
  deriving DecidableEq
open Stage

/-- Flame has a two-edge path; a distinct process has a bypass from ready and
can replace the flame after a safe state. No literal fire physics is asserted. -/
def finite : Model Bool Bool Stage where
  threat := fun p => ⟨p, true⟩
  occurs := fun p s t =>
    (p = false ∧ ((s = ready ∧ t = burning) ∨ (s = burning ∧ t = lost))) ∨
    (p = true ∧ (s = ready ∨ s = safe) ∧ t = lost)
  terminal := fun _ t => t = lost
  existsAt := fun s b => b = false ∨ s ≠ lost

def flame : Nat → Stage | 0 => ready | 1 => burning | _ => lost
def guarded : Nat → Stage | 0 => ready | _ => safe
def bypass : Nat → Stage | 0 => ready | _ => lost
def replacement : Nat → Stage | 0 => ready | 1 => safe | _ => lost
def blockFlame : Bool → Prop := fun p => p = false

/-- Positive two-step safety and actual interruption, plus omission controls.
The loss-coverage omission uses an unrepresented loss; wrong-bearer deletion
and mere label deletion leave the original destructive path intact. -/
def Controls : Prop :=
  (Interrupted finite false flame guarded 0 ∧
    Admissible finite blockFlame guarded 2 ∧ LossCovered finite guarded 2 true ∧
    NoBypass finite blockFlame guarded 2 true ∧ ProtectedInterval finite guarded 2 true) ∧
  (¬ removeThreat (finite.threat false) (fun _ => True) (finite.threat false) ∧
    Destroys finite false (flame 1) (flame 2) true ∧
    ¬ ProtectedInterval finite flame 2 true) ∧
  (Admissible finite blockFlame bypass 1 ∧ LossCovered finite bypass 1 true ∧
    ¬ NoBypass finite blockFlame bypass 1 true ∧ ¬ ProtectedInterval finite bypass 1 true) ∧
  (Admissible finite blockFlame replacement 2 ∧ LossCovered finite replacement 2 true ∧
    ¬ NoBypass finite blockFlame replacement 2 true ∧
    ¬ ProtectedInterval finite replacement 2 true) ∧
  (¬ removeThreat (⟨false, false⟩ : Threat Bool) (fun _ => True) ⟨false, false⟩ ∧
    Admissible finite (fun p => finite.threat p = ⟨false, false⟩) flame 2 ∧
    ¬ ProtectedInterval finite flame 2 true) ∧
  (LossCovered finite flame 2 true ∧ NoBypass finite blockFlame flame 2 true ∧
    ¬ Admissible finite blockFlame flame 2 ∧ ¬ ProtectedInterval finite flame 2 true) ∧
  (∃ m : Model Bool Bool Stage, m.occurs = finite.occurs ∧
    Admissible m blockFlame guarded 2 ∧ NoBypass m blockFlame guarded 2 true ∧
    m.existsAt (guarded 0) true ∧ ¬ LossCovered m guarded 2 true ∧
    ¬ ProtectedInterval m guarded 2 true) ∧
  (∃ m : Model Bool Bool Stage, ¬ m.existsAt (guarded 0) true ∧
    Admissible m blockFlame guarded 2 ∧ LossCovered m guarded 2 true ∧
    NoBypass m blockFlame guarded 2 true ∧ ¬ ProtectedInterval m guarded 2 true) ∧
  (∃ CausesIn : Bool → Bool → Unit → Prop,
    RealizesInterception finite guarding guarded 2 ∧ ProtectedInterval finite guarded 2 true ∧
    (∀ c x r, ¬ CausesIn c x r))
end TruthCore.Causality.ProtectiveProcess
