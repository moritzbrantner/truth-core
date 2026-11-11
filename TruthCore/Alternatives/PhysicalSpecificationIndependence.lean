module
public import TruthCore.Alternatives.PhysicalSpecificationPaths
public import TruthCore.Alternatives.PhysicalGround

/-!
Two controls on the restricted FO+reachability candidate of
`PhysicalSpecificationPaths`, replacing two weak controls there.

* `reachNontrivialControl`: one fixed reachability formula from the permitted anchor
  defines a target that is NOT constantly true on each carrier (the even numbers
  under the step-two graph on Nat; the anchor alone in the edgeless Bool graph), so
  reachability here separates reachable from unreachable vertices.
* `routeIndependenceControl`: two specified routes share one graph interpretation,
  hence one anchor and the same extension for every path formula, and both satisfy
  the ST I q.14 a.1 reading (`Route.Immaterial`); in one the anchor is composite and
  has intellect, in the other it is neither. So the reachability profile does not fix
  the existing Stage 2 composition and intellect predicates of `PhysicalGround.Route`.

Analyst formulation; attribution deferred. Graph edges are ordinary adjacency, not
causation, composition or bearing. Neither control maps the candidate language to an
original ground, so neither refutes or supports the root-route premise
STMT-IMMATERIAL-IS-INTELLECTUAL; the occurrence/property-to-bearer bridge stays open.
-/
@[expose] public section
namespace TruthCore.Alternatives.PhysicalSpecification
open FirstOrder TruthCore.Alternatives.PhysicalGround

/-! ## A non-trivial reachability target -/

/-- Nat under the step-two graph and Bool under the edgeless graph. -/
@[reducible] def evenDomain : Bool → Type | false => Nat | true => Bool

def evenAnchor : (b : Bool) → evenDomain b | false => 0 | true => false

/-- Ordinary adjacency: `y = x + 2` on Nat, no edges on Bool. -/
def stepTwo : (b : Bool) → evenDomain b → evenDomain b → Prop
  | false, x, y => y = x + 2
  | true, _, _ => False

@[instance_reducible] def evenModel (b : Bool) :
    Interpretation linkVocabulary Unit (evenDomain b) where
  model := {
    funMap := fun f _ => Empty.elim f.val
    RelMap := fun r xs => match r.val with | .edge => stepTwo b (xs 0) (xs 1) }
  parameter := fun _ => evenAnchor b

/-- The target: even numbers on Nat, the anchor alone on Bool. -/
def evenTarget : (b : Bool) → evenDomain b → Prop
  | false, x => Even x
  | true, x => x = false

/-- The one formula: the free object is reachable from the permitted anchor. -/
def anchorReach : PathFormula linkVocabulary (Unit ⊕ {_a : Unit // True}) :=
  .reach ⟨Link.edge, trivial⟩ (Sum.inr ⟨(), trivial⟩) (Sum.inl ())

/-- `anchorReach` defines `evenTarget` on both carriers (so `VaryingPathDefinability`
holds with a non-constant target), each carrier has an unreachable vertex (1 on Nat,
true on Bool), and the Nat target is reached through a vertex other than the anchor
(2). No FO undefinability claim. -/
def reachNontrivialControl : Prop :=
  VaryingPathDefinability linkVocabulary evenDomain evenModel (fun _ : Unit => True)
    (fun _ => True) evenTarget ∧
  (∀ b x, anchorReach.realize (evenModel b).model
      (Sum.elim (fun _ => x) (fun a => (evenModel b).parameter a.val)) ↔ evenTarget b x) ∧
  ¬ evenTarget false 1 ∧ ¬ evenTarget true true ∧ evenTarget false 2

/-! ## Independence of the Stage 2 route predicates from the profile -/

/-- One graph interpretation and one `PhysicalGround.Route` (the Stage 2 parameters of
`godHasIntellect`) on the SAME carrier. Nothing links the two components. -/
structure SpecifiedRoute (D : Type) where
  graph : Interpretation linkVocabulary Unit D
  route : Route D Unit Unit

/-- The extension of a path formula at the object `x`, with the route's anchor. -/
def SpecifiedRoute.realizes {D : Type} (s : SpecifiedRoute D)
    (p : PathFormula linkVocabulary (Unit ⊕ {_a : Unit // True})) (x : D) : Prop :=
  p.realize s.graph.model (Sum.elim (fun _ => x) (fun a => s.graph.parameter a.val))

/-- Same reachability profile: the same anchor and the same extension for EVERY
restricted path formula on the shared carrier. -/
def SameReachProfile {D : Type} (s t : SpecifiedRoute D) : Prop :=
  s.graph.parameter () = t.graph.parameter () ∧ ∀ p x, s.realizes p x ↔ t.realizes p x

/-- Route parameters with a composite anchor 0 that has intellect. The anchor is not
matter-form and no component, so `Route.Immaterial` itself requires its intellect. -/
def intellectualRoute : Route Nat Unit Unit where
  MatterForm := fun x => x ≠ 0
  Composite := fun _ => True
  HasIntellect := fun x => x = 0
  HasWill := fun x => x = 0
  ComponentOf := fun _ _ => False
  PriorSimply := fun _ _ => False
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  InAct := fun _ _ => True
  MoreIn := fun _ _ _ => False
  CausesIn := fun _ _ _ => False
  esse := ()

/-- Route parameters in which nothing is composite or has intellect. The anchor 0 is
not matter-form but is a component of 2, so `Route.Immaterial` does not apply to it. -/
def componentRoute : Route Nat Unit Unit where
  MatterForm := fun x => x ≠ 0
  Composite := fun _ => False
  HasIntellect := fun _ => False
  HasWill := fun _ => False
  ComponentOf := fun x y => x = 0 ∧ y = 2
  PriorSimply := fun _ _ => False
  essenceOf := fun _ => ()
  esseOf := fun _ => ()
  InAct := fun _ _ => True
  MoreIn := fun _ _ _ => False
  CausesIn := fun _ _ _ => False
  esse := ()

/-- There are two specified routes on Nat with the same non-trivial reachability
profile (the anchor reaches exactly the even numbers), both satisfying the
ST I q.14 a.1 reading at their route parameters, such that the anchor is composite and
has intellect in the first and is neither composite nor has intellect in the second.
A witness of independence inside this candidate language only. -/
def routeIndependenceControl : Prop :=
  ∃ s t : SpecifiedRoute Nat,
    SameReachProfile s t ∧
    (∀ x, s.realizes anchorReach x ↔ Even x) ∧
    s.route.Immaterial ∧ t.route.Immaterial ∧
    s.route.Composite (s.graph.parameter ()) ∧ s.route.HasIntellect (s.graph.parameter ()) ∧
    ¬ t.route.Composite (s.graph.parameter ()) ∧ ¬ t.route.HasIntellect (s.graph.parameter ())

end TruthCore.Alternatives.PhysicalSpecification
