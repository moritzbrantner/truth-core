import TruthCore.Causality.WorldSourceRegress
import Mathlib.Data.Int.Basic

/-! Analyst-defined structural constraints on the existing causal graph.
Instantiate G by actualGraph m w for one fixed world: connectivity is on actual
causal nodes, not on modal accessibility. Unique predecessors are a strong open
restriction, not a general law about efficient causation. -/
namespace TruthCore.Causality.SourceForest
open TruthCore.Logic.Regress

def WeaklyConnected {Node : Type} (G : Graph Node) : Prop :=
  ∀ a b, Relation.EqvGen G.edge a b

def UniquePredecessor {Node : Type} (G : Graph Node) : Prop :=
  Relator.LeftUnique G.edge

/-- Standard confluence of upstream finite rewriting, expressed using Mathlib
reflexive-transitive closure and Join. Two upstream paths from one node can
be extended to a common ancestor; a common source is not assumed. -/
def UpstreamConfluent {Node : Type} (G : Graph Node) : Prop :=
  ∀ a b c, Relation.ReflTransGen (fun x y => G.edge y x) a b →
    Relation.ReflTransGen (fun x y => G.edge y x) a c →
    Relation.Join (Relation.ReflTransGen (fun x y => G.edge y x)) b c

def AtMostOneSource {Node : Type} (G : Graph Node) : Prop :=
  ∀ a b, G.Source a → G.Source b → a = b

def WellFoundedEdges {Node : Type} (G : Graph Node) : Prop := WellFounded G.edge

def Populated {Node : Type} (_G : Graph Node) : Prop := Nonempty Node

/-- Unique source and a finite upstream path from every node to that same
source. The source may have no outgoing edge in a singleton graph. -/
def RootedAtUniqueSource {Node : Type} (G : Graph Node) : Prop :=
  ∃ s, G.Source s ∧ (∀ t, G.Source t → t = s) ∧
    ∀ x, FiniteCausalPath G.edge x s

inductive ForkNode | a | b | c
  deriving DecidableEq

def fork : Graph ForkNode := ⟨fun y x => (y = .a ∨ y = .b) ∧ x = .c⟩
def isolated : Graph Bool := ⟨fun _ _ => False⟩
/-- Integers index causal nodes, not time or worlds. -/
def chain : Graph Int := ⟨fun y x => y = x + 1⟩
def empty : Graph Empty := ⟨fun _ _ => False⟩

/-- Four fixed logical controls, not asserted metaphysical possibilities.
The fork drops unique predecessor, isolated nodes drop connectivity, the
integer chain drops WF, and Empty drops population. -/
def OmissionControls : Prop :=
  (WeaklyConnected fork ∧ WellFoundedEdges fork ∧ fork.NoCycles ∧
    ¬ UniquePredecessor fork ∧ fork.Source .a ∧ fork.Source .b ∧
    ForkNode.a ≠ .b) ∧
  (UniquePredecessor isolated ∧ WellFoundedEdges isolated ∧
    ¬ WeaklyConnected isolated ∧ isolated.Source false ∧ isolated.Source true) ∧
  (WeaklyConnected chain ∧ UniquePredecessor chain ∧ AtMostOneSource chain ∧
    ¬ WellFoundedEdges chain ∧ ¬ ∃ s, chain.Source s) ∧
  (WeaklyConnected empty ∧ UniquePredecessor empty ∧ WellFoundedEdges empty ∧
    AtMostOneSource empty ∧ ¬ Populated empty ∧ ¬ ∃ s, empty.Source s)

inductive DiamondNode | root | left | right | tip
  deriving DecidableEq

def diamond : Graph DiamondNode := ⟨fun y x =>
  (y = .root ∧ (x = .left ∨ x = .right)) ∨
  ((y = .left ∨ y = .right) ∧ x = .tip)⟩

/-- A fixed diamond has two immediate parents at tip but confluent upstream
paths. This witnesses a strict weakening, not a universal claim about causes. -/
def ConfluenceStrictnessControl : Prop :=
  UpstreamConfluent diamond ∧ WeaklyConnected diamond ∧
    WellFoundedEdges diamond ∧ ¬ UniquePredecessor diamond ∧
    RootedAtUniqueSource diamond
end TruthCore.Causality.SourceForest
