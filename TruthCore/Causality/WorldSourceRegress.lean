import Mathlib.Basic.Finite.Defs
import TruthCore.Logic.Regress
import TruthCore.German.Kant.CosmologicalInference
import TruthCore.Results.Causality.GroundingAllowsRegress.Solution

/-! World-local actual-node source/regress classification. Edge y x means
upstream y causes x in ONE fixed world. FiniteCausalPath edge x s walks
upstream from x to s; nil is not a self-cause. Nat chain indices count links,
not temporal instants. Restricting the carrier to actual nodes prevents absent
isolated candidates from serving as starters. No causal endpoint-soundness,
modal accessibility, finite branching or cross-world union condition is assumed.
All sources and regress are relative to the chosen ordinary causal relation. -/
namespace TruthCore.Causality.WorldSourceRegress
open TruthCore.German.Kant.CosmologicalInference
open TruthCore.Logic.Regress

abbrev Actual {World Being : Type} (m : Ontic World Being) (w : World) :=
  {x : Being // m.ExistsAt w x}

def actualGraph {World Being : Type} (m : Ontic World Being) (w : World) :
    Graph (Actual m w) := ⟨fun y x => m.Causes w y.val x.val⟩

/-- Parameterized use of the existing finite upstream path and Graph.Source.
A source may be isolated and need not be the only source. -/
def SourcePath {Node : Type} (G : Graph Node) (x : Node) : Prop :=
  ∃ s, FiniteCausalPath G.edge x s ∧ G.Source s

/-- A genuine anchored chain of distinct actual nodes in a single world;
not a traversal between possible worlds or temporal instants. -/
def AnchoredRegress {Node : Type} (G : Graph Node) (x : Node) : Prop :=
  ∃ f : Nat → Node, f 0 = x ∧ Function.Injective f ∧
    ∀ n, G.edge (f (n + 1)) (f n)

/-- Acyclicity only inside each world's actual-node graph. -/
def ActualAcyclic {World Being : Type} (m : Ontic World Being) : Prop :=
  ∀ w, (actualGraph m w).NoCycles

/-- Existential world labels. A starter world has some existing source, not
necessarily a source for every node, a temporal beginning, or a unique cause. -/
def StarterWorlds {World Being : Type} (m : Ontic World Being) : Set World :=
  {w | ∃ s : Actual m w, (actualGraph m w).Source s}

def RegressWorlds {World Being : Type} (m : Ontic World Being) : Set World :=
  {w | ∃ x : Actual m w, AnchoredRegress (actualGraph m w) x}

/-- Pointwise coverage, its exact population-set projection, and the finite
actual-graph corollary. The two horns/world sets are allowed to overlap.
Population is guarded explicitly; an empty world gets neither world label. -/
def WorldClassification {World Being : Type} (m : Ontic World Being) : Prop :=
  (∀ w (x : Actual m w), SourcePath (actualGraph m w) x ∨
    AnchoredRegress (actualGraph m w) x) ∧
  ({w | ∃ x, m.ExistsAt w x} = StarterWorlds m ∪ RegressWorlds m) ∧
  ∀ w, Finite (Actual m w) → (∃ x, m.ExistsAt w x) → w ∈ StarterWorlds m

/-- Infinite literal-link interpretation, not a finite-model registration.
Every candidate exists in the sole world, and old link is reused unchanged. -/
def overlap : Ontic Unit (Option Nat) where
  frame := ⟨fun _ _ => True⟩
  ExistsAt := fun _ _ => True
  Causes := fun _ => TruthCore.Results.Causality.GroundingAllowsRegress.link

def overlapNode : Actual overlap () := ⟨some 0, True.intro⟩

/-- The SAME actual some 0 has a source path and an injective anchored regress
on an acyclic graph, while it is inaccessible. Thus SourcePath is not Acc,
and neither the pointwise fork nor the world labels form an exclusive split. -/
def OverlapControl : Prop :=
  ActualAcyclic overlap ∧ SourcePath (actualGraph overlap ()) overlapNode ∧
  AnchoredRegress (actualGraph overlap ()) overlapNode ∧
  ¬ Acc (actualGraph overlap ()).edge overlapNode ∧
  () ∈ StarterWorlds overlap ∩ RegressWorlds overlap
end TruthCore.Causality.WorldSourceRegress

namespace TruthCore.Causality.WorldSourceRegress
/-- Every actual node of every finite actual graph has its own finite path to
an existing source. Empty actual carriers make the guarded conclusion vacuous;
no common source for all nodes or worlds, outgoing effect, or time is claimed. -/
def FiniteActualAllSourcePaths {World Being : Type}
    (m : TruthCore.German.Kant.CosmologicalInference.Ontic World Being) : Prop :=
  ∀ w, Finite (Actual m w) → ∀ x : Actual m w, SourcePath (actualGraph m w) x
end TruthCore.Causality.WorldSourceRegress
