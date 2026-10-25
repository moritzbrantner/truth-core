import TruthCore.Modal.ResearchFinite

/-!
Issue #273: logical existence, described objects, and explanatory independence.
Russell, Logical Atomism V pp.66–68 and VI pp.86–87 motivate the two
quantifier analyses. V p.72 expressly leaves the analysis of general facts open.
The finite grounding and varying-domain tests below are modern stipulated
alternatives, not reconstructions of Russell's full ontology.

Reuse boundary: existing ParticipationGrounding and ExplanationOrder relations
have participation/moral relata. These instantiation facts are not those facts;
reusing their tag types would falsely identify the meanings. Modal frames and
truth reuse the shared #261 semantics without change.
-/
namespace TruthCore.Modern.Russell.Existence

universe u
/-- A1, nonempty predication. The domain may be empty. This is not a cause. -/
def ExistsPred {E : Type u} (F : E → Prop) : Prop := ∃ x, F x
/-- At most one is separate from existence, including on the empty extension. -/
def AtMostOne {E : Type u} (F : E → Prop) : Prop :=
  ∀ x y, F x → F y → x = y
/-- VI pp.86–87's identity-characterization of a definite description. -/
def DescriptionExists {E : Type u} (F : E → Prop) : Prop :=
  ∃ c, ∀ x, F x ↔ x = c
/-- Constructive typed analysis; no claim of metaphysical explanatory adequacy. -/
def DescriptionLaw : Prop :=
  ∀ (E : Type) (F : E → Prop),
    DescriptionExists F ↔ ExistsPred F ∧ AtMostOne F

inductive Entity where | a | b deriving Repr
abbrev Extension := Entity → Bool
def Inst (F : Extension) (x : Entity) : Prop := F x = true
/-- Exhaustive two-label carrier; labels are not actual persons or possibilities. -/
def entities : List Entity := [.a, .b]
def none : Extension := fun _ => false
def singleA : Extension
  | .a => true
  | .b => false
def singleB : Extension
  | .a => false
  | .b => true
def both : Extension := fun _ => true
/-- Actual finite multiplicity for this exhaustively specified carrier only. -/
def count (F : Extension) : Nat :=
  (if F .a then 1 else 0) + (if F .b then 1 else 0)
/-- Same existential truth need not fix number or the identities of witnesses. -/
def CardinalityBoundary : Prop :=
  ¬ ExistsPred (Inst none) ∧ AtMostOne (Inst none) ∧
  ExistsPred (Inst singleA) ∧ ExistsPred (Inst both) ∧
  count none = 0 ∧ count singleA = 1 ∧ count both = 2 ∧
  count singleA ≠ count both ∧
  (ExistsPred (Inst singleA) ↔ ExistsPred (Inst singleB)) ∧
  Inst singleA .a ∧ ¬ Inst singleB .a ∧
  DescriptionExists (Inst singleA) ∧ ¬ DescriptionExists (Inst both)

/-- A candidate basis is a separate fact tag, not a relabeling of instantiation.
The test stipulates its truth; no actual constitutive essence is asserted. -/
inductive Fact where
  | basis : Entity → Fact
  | instance : Entity → Fact
  | inhabited
abbrev Grounding := Fact → Fact → Prop
/-- Common non-explanatory truth assignment, including the same candidate basis. -/
def FactTrue (F : Extension) : Fact → Prop
  | .basis _ => True
  | .instance x => Inst F x
  | .inhabited => ExistsPred (Inst F)
def emptyGround : Grounding := fun _ _ => False
/-- A single directed, stipulated explanatory edge; no causal temporal claim. -/
def linkedGround : Grounding := fun p q => p = .basis .a ∧ q = .instance .a
def Asymmetric (g : Grounding) : Prop := ∀ p q, g p q → ¬ g q p
def Sound (F : Extension) (g : Grounding) : Prop :=
  ∀ p q, g p q → FactTrue F p ∧ FactTrue F q
/-- A2's additional tested sufficiency bridge: all admitted explanatory expansions
of the fixed extension must agree on their directed grounding facts. This is
only one precise explanatory-exhaustiveness target, not all of Russell's syntax. -/
def GroundingDetermined (F : Extension) : Prop :=
  ∀ g h, Asymmetric g → Asymmetric h → Sound F g → Sound F h →
    ∀ p q, g p q ↔ h p q
/-- Logical truth conditions alone underdetermine grounding even among sound,
asymmetric expansions. This is not inconsistency or a rejection of primitives. -/
def GroundingBoundary : Prop :=
  ExistsPred (Inst singleA) ∧
  Asymmetric emptyGround ∧ Asymmetric linkedGround ∧
  Sound singleA emptyGround ∧ Sound singleA linkedGround ∧
  linkedGround (.basis .a) (.instance .a) ∧
  ¬ emptyGround (.basis .a) (.instance .a) ∧
  ¬ GroundingDetermined singleA

/-- Explicitly open realization premise for the selected test predicate. -/
def Realized (F : Extension) : Prop := ExistsPred (Inst F)
/-- One optional sufficient bridge from instantiation to a specifically tagged
basis ground. It is not attributed to Russell, not implied by A1, and not
asserted to be the only possible explanatory norm. -/
def InstanceBasisLaw (F : Extension) (g : Grounding) : Prop :=
  ∀ x, Inst F x → g (.basis x) (.instance x)
def GroundedExistence (F : Extension) (g : Grounding) : Prop :=
  ∃ x, Inst F x ∧ g (.basis x) (.instance x)
/-- Conditional projection plus omitted-premise witnesses: nonemptiness with
empty grounding fails; the basis law on an empty extension is vacuous. -/
def GroundingProjection (F : Extension) (g : Grounding) : Prop :=
  GroundedExistence F g ∧ ¬ GroundedExistence singleA emptyGround ∧
  InstanceBasisLaw none emptyGround ∧ ¬ Realized none

/-- World-relative actual domain, a modern alternative to a genuinely denoting
name at a fixed context; the outer carrier is not assumed actual at every world. -/
abbrev ActualAt := Bool → Entity → Prop
def actual : ActualAt
  | false, .a => True
  | false, .b => False
  | true, .a => False
  | true, .b => True
/-- A genuine name at the selected context has an actual referent by its typing.
This contextual condition makes no assertion of modal necessary existence. -/
structure StrictNameAt (A : ActualAt) (w : Bool) where
  referent : Entity
  denotes : A w referent
/-- A conventional name token may instead fail to denote in the alternative.
This is the contrast with Russell's strict use of genuine name, not his theory. -/
def token : Bool → Option Entity := fun _ => some .a
def DenotesAt (A : ActualAt) (w : Bool) (n : Option Entity) : Prop :=
  ∃ x, n = some x ∧ A w x
/-- Reuse the shared branching frame and formula semantics for varying existence. -/
def existenceValuation : TruthCore.Modal.Valuation Bool Entity := actual
def IndividualBoundary : Prop :=
  (∀ w, ExistsPred (actual w)) ∧
  actual false .a ∧ ¬ actual true .a ∧
  DenotesAt actual false (token false) ∧ ¬ DenotesAt actual true (token true) ∧
  (∃ n : StrictNameAt actual false, n.referent = .a) ∧
  (∀ w (n : StrictNameAt actual w), actual w n.referent) ∧
  ¬ TruthCore.Modal.Holds TruthCore.Modal.ResearchFinite.branching.frame
    existenceValuation false (.box (.atom .a)) ∧
  TruthCore.Modal.Holds TruthCore.Modal.ResearchFinite.branching.frame
    existenceValuation false (.diamond (.atom .b))

/-- Executable extension table. No claim of enumerating metaphysical realities. -/
def report : String := reprStr ([count none, count singleA, count singleB, count both],
  entities.map (fun x => (singleA x, singleB x, both x)))
#guard count none == 0
#guard count singleA == 1
#guard count singleB == 1
#guard count both == 2
end TruthCore.Modern.Russell.Existence
