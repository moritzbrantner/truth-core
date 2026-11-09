module

public import TruthCore.Explanation.WholeSeriesReason

/-!
Two analyst adequacy policies, not historical readings or established premises.
The weak policy accepts the existing reason-guided optimal exercise, including
ties. The stronger policy additionally requires execution of a supplied ordered
agenda: scan it and take the first feasible optimum. The agenda is supplied
independently of the actual choice, is fixed in uniform comparisons, and is NOT
defined by sorting the observed outcome first. Its philosophical authority,
content relevance, direction and independent calibration remain OPEN. This is
one positive procedural selection account, not an exhaustive account of agency.
-/
@[expose] public section
namespace TruthCore.Explanation.WholeSeriesChoicePolicies
open TruthCore.Explanation.PSRStrength TruthCore.Explanation.WholeSeriesReason
variable {W B F O : Type}

/-- Feasible with no strictly better feasible competitor. -/
def Optimal (S : Selection W B F O) (w : W) (b : B) (r : F) (o : O) : Prop :=
  S.admissible w b o ∧ ∀ p, S.admissible w b p → ¬ S.better w b r p o

/-- Positive scanning rule. A rejected head must fail optimality; skipping a tied
optimal head is forbidden. Empty agendas never select. No existence or
completeness of the supplied agenda is implicit. -/
def Picks (eligible : O → Prop) : List O → O → Prop
  | [], _ => False
  | h :: t, o => (eligible h ∧ o = h) ∨ (¬ eligible h ∧ Picks eligible t o)

/-- Stronger local analyst sibling: the original complete whole-order exercise
plus the positive procedural selection rule. Original entailing sibling unchanged. -/
structure SelectedWholeExercise (A : Arena W B F)
    (carries : W → B → F → Prop) (S : Selection W B F O)
    (agenda : List O) (a : W) extends ReasonGuidedWholeExercise A carries S a where
  selected : Picks (Optimal S a bearer content) agenda option

/-- Existential local stronger policy. Actual exercise, necessary bearer and all
fact content are inherited, not inferred from the agenda. -/
def HasSelectedWholeExercise (A : Arena W B F)
    (carries : W → B → F → Prop) (S : Selection W B F O)
    (agenda : List O) (a : W) : Prop :=
  Nonempty (SelectedWholeExercise A carries S agenda a)

/-- Uniform weak policy ranges over EVERY recorded choice, not just one actual
whole-order exercise. It does not assert that any choice occurs. -/
def UniformOptimal (S : Selection W B F O) : Prop :=
  ∀ w b r o, S.chooses w b o → Optimal S w b r o

/-- Uniform stronger policy: every choice executes the SAME supplied agenda.
It does not assert choice totality, agenda coverage, or nonempty optima. -/
def UniformSelected (S : Selection W B F O) (agenda : List O) : Prop :=
  ∀ w b r o, S.chooses w b o → Picks (Optimal S w b r) agenda o

/-- Fully extensional fact signature, not an existence-only or finite fact list.
The same necessary bearer exists at both worlds. No efficient causation supplied. -/
def arena : Arena Bool Unit (Bool → Prop) where
  ontic := { frame := ⟨fun _ _ => True⟩, ExistsAt := fun _ _ => True,
             Causes := fun _ _ _ => False }
  holds := fun w f => f w
  exist := fun _ _ => True
  explains := fun _ _ _ => False
  conjunct := fun g f => ∀ w, f w → g w

/-- Both full valuations are tied optima; actual choices alternate. This order
is fixed before any actual choice, not extracted from its truth. -/
def tied : Selection Bool Unit (Bool → Prop) Bool where
  valuation := fun o f => f o
  admissible := fun _ _ _ => True
  better := fun _ _ _ _ _ => False
  chooses := fun w _ o => o = w

/-- Reuses the ORIGINAL exercise type, with genuinely contingent choice and
necessary content/bearer; no truth-entailing sufficiency is asserted. -/
def exercise : ReasonGuidedWholeExercise arena (fun _ _ _ => True) tied false where
  bearer := ()
  content := fun _ => True
  actual := trivial
  necessary := fun _ _ => trivial
  realized := trivial
  obtains := trivial
  option := false
  feasible := trivial
  chosen := rfl
  optimal := fun _ _ h => h
  complete := fun _ => Iff.rfl
  contingentExercise := ⟨true, trivial, Bool.noConfusion⟩

/-- A non-total choice policy: the agent chooses at false and abstains at true.
The agenda and optimality remain fixed; uniform selection does not imply that
this contingent exercise repeats at every world. -/
def selective : Selection Bool Unit (Bool → Prop) Bool :=
  { tied with chooses := fun w _ o => w = false ∧ o = false }

def selectiveExercise : ReasonGuidedWholeExercise arena (fun _ _ _ => True) selective false where
  bearer := ()
  content := fun _ => True
  actual := trivial
  necessary := fun _ _ => trivial
  realized := trivial
  obtains := trivial
  option := false
  feasible := trivial
  chosen := ⟨rfl, rfl⟩
  optimal := fun _ _ h => h
  complete := fun _ => Iff.rfl
  contingentExercise := ⟨true, trivial, fun h => Bool.noConfusion h.1⟩

/-- Closed obligations: scanning has a unique selected option and exists exactly
when the finite agenda contains an eligible option; uniform selected implies
uniform optimal; fixed eligibility plus the same agenda forces stable selected
output only WHEN actual and accessible selections are both supplied. The full
fact-domain tied exercise is nonvacuous locally; weak uniform policy holds but
strong uniform policy fails. Reversed/empty agenda omissions retain that SAME
whole-order exercise. No global feasibility or actuality is inferred. -/
def Certificates : Prop :=
  (∀ (O : Type) (P : O → Prop) (l : List O) (x y : O),
    Picks P l x → Picks P l y → x = y) ∧
  (∀ (O : Type) (P : O → Prop) [DecidablePred P] (l : List O),
    (∃ x, Picks P l x) ↔ ∃ x, x ∈ l ∧ P x) ∧
  (∀ (W B F O : Type) (S : Selection W B F O) (l : List O),
    UniformSelected S l → UniformOptimal S) ∧
  (∀ (O : Type) (P Q : O → Prop) (l : List O) (x y : O),
    (∀ o, P o ↔ Q o) → Picks P l x → Picks Q l y → x = y) ∧
  Nonempty (SelectedWholeExercise arena (fun _ _ _ => True) tied [false, true] false) ∧
  UniformOptimal tied ∧
  ¬ UniformSelected tied [false, true] ∧
  ¬ Picks (Optimal tied false () (fun _ => True)) [true, false] false ∧
  ¬ Picks (Optimal tied false () (fun _ => True)) [] false ∧
  (∀ (W B F O : Type) (A : Arena W B F) (carries : W → B → F → Prop)
    (S : Selection W B F O) (agenda : List O) (a : W),
    HasSelectedWholeExercise A carries S agenda a → HasReasonGuidedWholeExercise A carries S a) ∧
  (∀ (O : Type) (P : O → Prop) (l : List O),
    (∀ o, ¬ P o) → ¬ ∃ o, Picks P l o) ∧
  (Nonempty (SelectedWholeExercise arena (fun _ _ _ => True) selective [false, true] false) ∧
    UniformSelected selective [false, true])
end TruthCore.Explanation.WholeSeriesChoicePolicies
