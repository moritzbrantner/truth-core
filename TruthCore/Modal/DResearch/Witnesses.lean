import TruthCore.Modal.DResearch.Laws

namespace TruthCore.Modal.DResearch
open TruthCore.Modal.ResearchFixture
open TruthCore.Modal.ResearchFinite (Model eval witnesses counterexamples)
open TruthCore.Isabelle.AFP.GoedelGod (Box Dia)
open TruthCore.Modern.Hume.Conceivability (Contingent)

inductive PocketWorld where
  | root | collapse | left | right | away
  deriving DecidableEq, Repr
instance : OfNat PocketWorld 0 := ⟨.root⟩
instance : OfNat PocketWorld 1 := ⟨.collapse⟩
instance : OfNat PocketWorld 2 := ⟨.left⟩
instance : OfNat PocketWorld 3 := ⟨.right⟩
instance : OfNat PocketWorld 4 := ⟨.away⟩
/-- Explicit finite serial graph; see the edge table in docs/modal-d.md. -/
def pocket : Model PocketWorld Unit where
  worlds := [.root, .collapse, .left, .right, .away]
  complete := by
    intro w
    cases w with
    | root => exact .head _
    | collapse => exact .tail _ (.head _)
    | left => exact .tail _ (.tail _ (.head _))
    | right => exact .tail _ (.tail _ (.tail _ (.head _)))
    | away => exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
  edge := fun w v => match w with
    | .root => match v with
      | .root => false
      | .collapse => true
      | .left => true
      | .right => false
      | .away => false
    | .collapse => match v with
      | .root => false
      | .collapse => true
      | .left => false
      | .right => false
      | .away => false
    | .left => match v with
      | .root => false
      | .collapse => false
      | .left => false
      | .right => true
      | .away => false
    | .right => match v with
      | .root => false
      | .collapse => false
      | .left => true
      | .right => false
      | .away => false
    | .away => match v with
      | .root => false
      | .collapse => false
      | .left => false
      | .right => false
      | .away => true
  atom := fun w _ => match w with
    | .root => false
    | .collapse => true
    | .left => false
    | .right => false
    | .away => false

inductive ForkWorld where
  | root | left | right
  deriving DecidableEq, Repr
instance : OfNat ForkWorld 0 := ⟨.root⟩
instance : OfNat ForkWorld 1 := ⟨.left⟩
instance : OfNat ForkWorld 2 := ⟨.right⟩
/-- Explicit finite serial graph; see the edge table in docs/modal-d.md. -/
def fork : Model ForkWorld Unit where
  worlds := [.root, .left, .right]
  complete := by
    intro w
    cases w with
    | root => exact .head _
    | left => exact .tail _ (.head _)
    | right => exact .tail _ (.tail _ (.head _))
  edge := fun w v => match w with
    | .root => match v with
      | .root => false
      | .left => true
      | .right => true
    | .left => match v with
      | .root => false
      | .left => true
      | .right => false
    | .right => match v with
      | .root => false
      | .left => false
      | .right => true
  atom := fun w _ => match w with
    | .root => false
    | .left => true
    | .right => false

/-- Literal possible collapse does not propagate on serial frames, even when
there are no dead ends. The actual predicate and its contrary have witnesses
1 and 2 at the same root; no real-world contingency is assumed. -/
def PocketChecks : Prop :=
  Serial pocket.frame ∧ ¬ Reflexive pocket.frame ∧
  ¬ Symmetric pocket.frame ∧ ¬ Transitive pocket.frame ∧
  MC pocket.frame allPredicates 1 ∧ MC pocket.frame allPredicates 4 ∧
  ¬ MC pocket.frame allPredicates 0 ∧
  Dia pocket.frame (MC pocket.frame allPredicates) 0 ∧
  ¬ Box pocket.frame (MC pocket.frame allPredicates) 0 ∧
  Contingent pocket.frame (fun w => w = 1) 0 ∧
  Dia pocket.frame (fun w => w = 1) 0 ∧ (0 : PocketWorld) ≠ 1 ∧
  (pocket.frame.access 2 3 ∧ pocket.frame.access 3 2) ∧
  (∀ v, pocket.frame.access 2 v → v = 3) ∧
  (∀ v, pocket.frame.access 3 v → v = 2) ∧
  (¬ pocket.frame.access 0 4 ∧ ¬ pocket.frame.access 4 0) ∧
  (∀ v, pocket.frame.access 4 v ↔ v = 4) ∧
  witnesses pocket 0 (.atom ()) = [1] ∧
  counterexamples pocket 0 (.atom ()) = [2]

/-- Even necessary full collapse of all successors leaves the serial root
uncollapsed and permits contingency. □MC is thus not MC or world uniqueness. -/
def ForkChecks : Prop :=
  Serial fork.frame ∧ ¬ Reflexive fork.frame ∧ ¬ Symmetric fork.frame ∧
  MC fork.frame allPredicates 1 ∧ MC fork.frame allPredicates 2 ∧
  ¬ MC fork.frame allPredicates 0 ∧
  Dia fork.frame (MC fork.frame allPredicates) 0 ∧
  Box fork.frame (MC fork.frame allPredicates) 0 ∧
  Contingent fork.frame (fun w => w = 1) 0 ∧
  Dia fork.frame (fun w => w = 1) 0 ∧ (0 : ForkWorld) ≠ 1 ∧
  witnesses fork 0 (.atom ()) = [1] ∧
  counterexamples fork 0 (.atom ()) = [2]

/-- A deterministic, complete reproduction of both finite edge/truth tables.
Run #eval on this value in a file importing this module to inspect it. -/
def report : String :=
  let rows := fun (m : Model (PocketWorld) Unit) => m.worlds.map (fun w =>
    (w, m.worlds.map (fun v => (v, m.edge w v)),
      eval m w (.atom ()), eval m w (.box (.atom ())),
      eval m w (.diamond (.atom ())), witnesses m w (.atom ()),
      counterexamples m w (.atom ())))
  reprStr (rows pocket) ++ "\n" ++ reprStr (fork.worlds.map (fun w =>
    (w, fork.worlds.map (fun v => (v, fork.edge w v)),
      eval fork w (.atom ()), eval fork w (.box (.atom ())),
      eval fork w (.diamond (.atom ())), witnesses fork w (.atom ()),
      counterexamples fork w (.atom ()))))

#guard eval pocket 0 (.atom ()) == false
#guard eval pocket 0 (.diamond (.atom ())) == true
#guard eval pocket 0 (.diamond (.imp (.atom ()) .falsum)) == true
#guard eval pocket 0 (.box (.atom ())) == false
#guard eval fork 0 (.diamond (.atom ())) == true
#guard eval fork 0 (.diamond (.imp (.atom ()) .falsum)) == true
#guard eval fork 0 (.atom ()) == false

/-- Exact finite serial countermodel contract. -/
def WitnessChecks : Prop := PocketChecks ∧ ForkChecks
end TruthCore.Modal.DResearch
