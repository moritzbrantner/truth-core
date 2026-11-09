module

public import TruthCore.Explanation.PSRStrength

/-!
Analyst interpretations of whole-series reason, attribution deferred. The fact
sort must represent ALL contingent content, including laws and relations; no
finiteness or restriction to existence facts is imposed. Completeness of that
representation in reality is OPEN. These siblings do not complete the historical
sense merely by being available.
-/

@[expose] public section
namespace TruthCore.Explanation.WholeSeriesReason
open TruthCore.Explanation.PSRStrength

variable {W B F O : Type}

/-- Equality of the truth vector of EVERY actual contingent fact. No new
aggregate fact or substance called the universe is postulated. -/
def SameOrder (A : Arena W B F) (a v : W) : Prop :=
  ∀ f, Contingent A a f → (A.holds a f ↔ A.holds v f)

/-- A reason-content carried by an actually existing, necessarily existing
substance. `carries` is an explicit primitive realization relation: e.g. a
substance's act or nature content, not identity with its existence fact. Necessary
existence says nothing about necessity of that content. Causal productivity,
independence from the order, and the applicability of carries remain OPEN. -/
structure CarriedReason (A : Arena W B F) (carries : W → B → F → Prop)
    (a : W) where
  bearer : B
  content : F
  actual : A.ontic.ExistsAt a bearer
  necessary : ∀ v, Access A a v → A.ontic.ExistsAt v bearer
  realized : carries a bearer content
  obtains : A.holds a content

/-- Truth-entailing sibling: whenever this content obtains at an accessible
world, every actual contingent fact retains its truth. This includes law and
relation facts, and may be inconsistent with necessary content plus a genuine
contingent truth. Necessary bearer alone does not create that contradiction. -/
structure EntailingWholeReason (A : Arena W B F)
    (carries : W → B → F → Prop) (a : W) extends CarriedReason A carries a where
  discriminates : ∀ v, Access A a v → A.holds v content → SameOrder A a v

/-- Positive reason-guided selection vocabulary. Options are complete fact
assignments, not just existence histories. `admissible` and `better` are explicit
framework primitives (feasible exercises and strict reason preference). Their
interpretation, reason relevance, and freedom from circular outcome coding are
OPEN, not supplied by an arbitrary flag called sufficient. A reason-guided
choice need not have a uniquely best option. -/
structure Selection (W B F O : Type) where
  valuation : O → F → Prop
  admissible : W → B → O → Prop
  better : W → B → F → O → O → Prop
  chooses : W → B → O → Prop

/-- Nonnecessitating sibling: an actual exercise chooses a feasible option with
no strictly better feasible rival under this reason; its complete valuation
realizes the actual fact order. The SAME exercise is absent at an accessible
world. No necessity of content, unique optimum, or truth-entailing rule is
assumed. Optimality alone is not claimed to establish explanatory adequacy. -/
structure ReasonGuidedWholeExercise (A : Arena W B F)
    (carries : W → B → F → Prop) (S : Selection W B F O) (a : W)
    extends CarriedReason A carries a where
  option : O
  feasible : S.admissible a bearer option
  chosen : S.chooses a bearer option
  optimal : ∀ o, S.admissible a bearer o → ¬ S.better a bearer content o option
  complete : ∀ f, S.valuation option f ↔ A.holds a f
  contingentExercise : ∃ v, Access A a v ∧ ¬ S.chooses v bearer option

/-- Open analyst proposition: an entailing carried whole-series reason exists. -/
def HasEntailingWholeReason (A : Arena W B F)
    (carries : W → B → F → Prop) (a : W) : Prop :=
  Nonempty (EntailingWholeReason A carries a)

/-- Open analyst proposition: a reason-guided contingent whole-order exercise exists. -/
def HasReasonGuidedWholeExercise (A : Arena W B F)
    (carries : W → B → F → Prop) (S : Selection W B F O) (a : W) : Prop :=
  Nonempty (ReasonGuidedWholeExercise A carries S a)

end TruthCore.Explanation.WholeSeriesReason
