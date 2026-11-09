module

/-! Finite pragmatic response semantics for the q.19 will route. Analyst model,
attribution deferred. One end is tracked; false/true mean absent/possessed.
Actions acquire, retain, or ignore that end. Availability is ability, and rank
is primitive appetitive attraction, not objective goodness, cognition, chosen
output or a utility maximizing policy. A map showing an end as good can have
all ranks zero. Calibration is an OPEN profile constraint: acquiring water when
absent and retaining it when possessed can outrank ignoring it. A merely
contemplative representer or aversion to the represented end is excluded by
calibration, not disproved. No passive faculty or temporal change is required
of a divine subject: application beyond this finite pragmatic model is OPEN. -/

@[expose] public section
namespace TruthCore.Causality.PossessionSensitiveAppetite

inductive Action where
  | acquire | retain | ignore
  deriving DecidableEq

/-- Response type changes with possession; retaining is not deficient seeking. -/
def response : Bool → Action
  | false => .acquire
  | true => .retain

/-- Successful action/end relation. Ignoring never counts as seeking or resting.
Retaining an absent end and acquiring an already possessed end are excluded. -/
def serves (p : Bool) (a : Action) : Prop :=
  (p = false ∧ a = .acquire) ∨ (p = true ∧ a = .retain)

/-- Applying an action gives the next possession state of this one end. -/
def next (p : Bool) : Action → Bool
  | .acquire => true
  | .retain => p
  | .ignore => p

structure Profile where
  representedGood : Bool → Prop
  available : Bool → Action → Prop
  rank : Bool → Action → Nat

/-- OPEN, local and comparative only: no ranking of other actions or goods. -/
def Calibration (m : Profile) : Prop :=
  ∀ p, m.representedGood p → m.rank p .ignore < m.rank p (response p)

/-- OPEN ability constraint, restricted to the represented states used. -/
def Availability (m : Profile) : Prop :=
  ∀ p, m.representedGood p → m.available p (response p)

/-- Existential oriented ability, with appropriate action and possession result.
This does not assert an action is selected or exercised. -/
def Capacity (m : Profile) : Prop :=
  ∀ p, m.representedGood p → ∃ a, m.available p a ∧
    m.rank p .ignore < m.rank p a ∧ serves p a ∧ next p a = true

/-- Populated in BOTH possession states, holding representations fixed. -/
def responsive : Profile :=
  ⟨fun _ => True, fun _ _ => True,
    fun p a => if a = response p then 1 else 0⟩

def cognitiveOnly : Profile :=
  { responsive with rank := fun _ _ => 0 }

def unavailable : Profile :=
  { responsive with available := fun _ _ => False }

/-- Nonvacuity and two carrying-premise omissions on the same populated
representations. No choice/optimality/no-output controls are duplicated. -/
def Controls : Prop :=
  ((∀ p, responsive.representedGood p) ∧ Calibration responsive ∧
    Availability responsive ∧ Capacity responsive) ∧
  ((∀ p, cognitiveOnly.representedGood p) ∧ Availability cognitiveOnly ∧
    ¬ Calibration cognitiveOnly ∧ ¬ Capacity cognitiveOnly) ∧
  ((∀ p, unavailable.representedGood p) ∧ Calibration unavailable ∧
    ¬ Availability unavailable ∧ ¬ Capacity unavailable)
end TruthCore.Causality.PossessionSensitiveAppetite
