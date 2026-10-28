import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Logic.Relation
import TruthCore.Modal.Kripke

/-! Faithful mathematical adapters for the existing Kripke frame.

Digraph adjacency is exactly one-step accessibility, retaining direction and
self-loops. The explicit thin quiver uses PLift because Mathlib's arrows live
in Type while accessibility lives in Prop. It is a value, never a global
Quiver instance on World: different frames may coexist on the same carrier.

Quiver reachability includes nil paths and transitive closure. It does not
replace the one-step relation used by modal Holds; additional frame conditions
are required to identify reachability with accessibility. -/
namespace TruthCore.Modal.Frame

universe u
variable {World : Type u}

/-- Preserve the frame's directed accessibility relation literally. -/
def toDigraph (F : TruthCore.Modal.Frame World) : Digraph World :=
  ⟨F.access⟩

/-- Regard directed adjacency, including any self-loops, as accessibility. -/
def ofDigraph (G : Digraph World) : TruthCore.Modal.Frame World :=
  ⟨G.Adj⟩

/-- Explicit thin quiver for one particular frame; no instance is installed
on the raw world type, and edges keep their original direction. -/
@[instance_reducible]
def toQuiver (F : TruthCore.Modal.Frame World) : Quiver.{0} World where
  Hom a b := PLift (F.access a b)

end TruthCore.Modal.Frame
