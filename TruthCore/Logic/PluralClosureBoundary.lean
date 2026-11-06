module

/-!
Analyst comparison #1084 under #932; attribution deferred. One local two-atom
language and ONE truth/falsity-pair algebra interpret both matrices. Existing
Verificationism.Language and ReflectiveCoherence.Semantics require object
negation to be Lean negation; that would exclude the very gaps/gluts tested.
IntuitionisticKnowability uses different genuine Heyting operations. No existing
K3/LP matrix or neutral propositional syntax was found. This small grammar is
not a new general proof platform; no global completeness/join claim is made.

A belief pool is an extensional selected formula set, not an ought predicate.
Closure under both consequence relations is an EXTRA policy commitment. No
performance, categorical authority or actual truth of a selected formula follows.
-/

@[expose] public section
namespace TruthCore.Logic.PluralClosureBoundary

/-- Exactly two atoms; all finite formulas in this fixed signature. -/
inductive Formula where
  | atom : Bool → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  deriving DecidableEq, Repr

/-- Independent truth and falsity bits: T=(true,false), F=(false,true),
Neither=(false,false), Both=(true,true). Both is NOT `P ∧ ¬P` in Lean. -/
abbrev Value := Bool × Bool
abbrev Valuation := Bool → Value

def eval (v : Valuation) : Formula → Value
  | .atom a => v a
  | .neg a => ((eval v a).2, (eval v a).1)
  | .conj a b => ((eval v a).1 && (eval v b).1, (eval v a).2 || (eval v b).2)
  | .disj a b => ((eval v a).1 || (eval v b).1, (eval v a).2 && (eval v b).2)

/-- Designation reads the truth bit, allowing a simultaneous falsity bit. -/
def Designated (v : Valuation) (a : Formula) : Prop := (eval v a).1 = true

inductive Profile where | k3 | lp deriving DecidableEq

/-- K3 excludes Both at atoms; LP excludes Neither. The compositional algebra
is shared without relabeling negation between the two profiles. -/
def Admissible : Profile → Valuation → Prop
  | .k3, v => ∀ a, ¬ ((v a).1 = true ∧ (v a).2 = true)
  | .lp, v => ∀ a, (v a).1 = true ∨ (v a).2 = true

/-- Semantic designated-truth preservation, over every admitted valuation. -/
def Consequence (L : Profile) (Γ : List Formula) (a : Formula) : Prop :=
  ∀ v, Admissible L v → (∀ b ∈ Γ, Designated v b) → Designated v a

abbrev Pool := Formula → Prop

/-- A stipulated shared pool contains every finite-premise consequence of its
members. This is selection closure, not categorical authority or feasibility. -/
def Closed (L : Profile) (B : Pool) : Prop :=
  ∀ Γ a, (∀ b ∈ Γ, B b) → Consequence L Γ a → B a

/-- A profile's semantic theory of the same single initial premise. -/
def Theory (L : Profile) (g : Formula) : Pool := fun a => Consequence L [g] a

/-- A valuation's designated formulas; distinct from consequence over a profile. -/
def DesignatedPool (v : Valuation) : Pool := Designated v

def p : Formula := .atom false
def q : Formula := .atom true
def premise : Formula := .disj p (.conj q (.neg q))
def lemQ : Formula := .disj q (.neg q)
def conclusion : Formula := .conj p lemQ

/-- The distinct semantic moves and explicit failure of the joint target in
EACH relation. These statements concern the SAME syntax and truth tables. -/
def SemanticBoundary : Prop :=
  Consequence .k3 [premise] p ∧ ¬ Consequence .lp [premise] p ∧
  Consequence .lp [] lemQ ∧ ¬ Consequence .k3 [] lemQ ∧
  (∀ L a b, Consequence L [a, b] (.conj a b)) ∧
  ¬ Consequence .k3 [premise] conclusion ∧
  ¬ Consequence .lp [premise] conclusion

/-- ONE pool with the initial premise and both closure commitments admits the
joint target. These are conditional policy inputs, not inferred obligations. -/
def JointClosureLaw : Prop :=
  ∀ B : Pool, B premise → Closed .k3 B → Closed .lp B → B conclusion

/-- Delete either closure while retaining the other and the initial premise;
or delete initial acceptance while retaining both closures. Each omitted
input is explicitly false and the target remains unselected. -/
def DeletionControls : Prop :=
  (∃ B : Pool, B premise ∧ Closed .k3 B ∧ ¬ Closed .lp B ∧ ¬ B conclusion) ∧
  (∃ B : Pool, B premise ∧ Closed .lp B ∧ ¬ Closed .k3 B ∧ ¬ B conclusion) ∧
  (∃ B : Pool, Closed .k3 B ∧ Closed .lp B ∧ ¬ B premise ∧ ¬ B conclusion)

/-- A common closed pool is nontrivial. Two separately indexed pools preserve
their own closure and initial acceptance while BOTH reject the joint target.
No identity of validity relations or defeat of local pluralism follows. -/
def SurvivorControls : Prop :=
  (∃ B : Pool, B premise ∧ Closed .k3 B ∧ Closed .lp B ∧
    B conclusion ∧ ¬ B (.neg p)) ∧
  (∃ BK BL : Pool, BK premise ∧ BL premise ∧ Closed .k3 BK ∧ Closed .lp BL ∧
    ¬ BK conclusion ∧ ¬ BL conclusion)

/-- Joint policy consequence, genuinely incomparable matrices, three deletions
and common/indexed survivors. No global join=CPL or categorical norm theorem. -/
def Certificate : Prop :=
  SemanticBoundary ∧ JointClosureLaw ∧ DeletionControls ∧ SurvivorControls

end TruthCore.Logic.PluralClosureBoundary
