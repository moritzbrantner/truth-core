import TruthCore.Modal.Cube
import TruthCore.Isabelle.AFP.GoedelGod
import TruthCore.Logic.ExcludedMiddle
import TruthCore.Models.FiniteSupport

/-! Issue #437: a stipulated proposition G, not a definition of God or Scott's
individual property NE. Reuses the existing Kripke frame and Box/Dia semantics.
No source is attributed; metaphysical adequacy and either possibility premise
remain open. One-world conclusions concern successors of that world only. -/
namespace TruthCore.Modal.NecessaryIfExistent
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
universe u
variable {W : Type u}

/-- The boxed conditional □(G → □G), at the named standpoint. It differs from
G w → □G w, and from a conditional asserted at every world in the frame. -/
def NecessaryIf (F : Frame W) (G : MProp W) (w : W) : Prop :=
  Box F (fun v => G v → Box F G v) w

/-- A conditional only at the actual standpoint; it asserts no other world conditional. -/
def ActualConditional (F : Frame W) (G : MProp W) (w : W) : Prop :=
  G w → Box F G w

/-- The positive possibility burden: at least one accessible G-world. -/
def PossibleExistence (F : Frame W) (G : MProp W) (w : W) : Prop := Dia F G w
/-- The reverse possibility burden: an accessible world at which G fails. -/
def PossibleNonexistence (F : Frame W) (G : MProp W) (w : W) : Prop :=
  Dia F (fun v => ¬ G v) w
/-- Necessary G relative to the named standpoint, not frame-global truth. -/
def NecessaryExistence (F : Frame W) (G : MProp W) (w : W) : Prop := Box F G w
/-- Impossibility of G relative to the named standpoint. -/
def ImpossibleExistence (F : Frame W) (G : MProp W) (w : W) : Prop :=
  Box F (fun v => ¬ G v) w
/-- Coverage of the two necessary alternatives, with no exclusivity asserted. -/
def Coverage (F : Frame W) (G : MProp W) (w : W) : Prop :=
  NecessaryExistence F G w ∨ ImpossibleExistence F G w

/-- Three conditional conclusions, including coverage but not exclusivity.
The reverse takes possible nonexistence as seriously as possible existence. -/
def Matrix (F : Frame W) (G : MProp W) (w : W) : Prop :=
  (Dia F G w → Box F G w) ∧
  (Dia F (fun v => ¬ G v) w → Box F (fun v => ¬ G v) w) ∧
  (Box F G w ∨ Box F (fun v => ¬ G v) w)

/-- A certified conditional schema: K5 suffices, so S5 suffices. EM is explicit;
no claim that Euclideanness is a necessary or minimal frame characterization. -/
def Certificate : Prop :=
  ∀ (W : Type) (F : Frame W) (G : MProp W) (w : W),
    Euclidean F → NecessaryIf F G w → TruthCore.Logic.ExcludedMiddle → Matrix F G w

/-- Finite controls use ordinary Bool predicates and the existing frame API. -/
def universal : Frame Bool := ⟨fun _ _ => True⟩
def empty : Frame Bool := ⟨fun _ _ => False⟩
def identity : Frame Bool := ⟨fun x y => x = y⟩
def ascending : Frame Bool := ⟨fun x y => x = false ∨ y = true⟩
def G : MProp Bool := fun w => w = true

/-- Fixed omission and scope controls. S4 retains the boxed conditional but
fails all three conclusions. Universal S5 retains only the actual conditional
and fails all three. Empty K5 gives both boxes and neither possibility. Identity
S5 separates component necessity from frame-global truth. Constant universal
models witness both rival possibilities separately; neither is established. -/
def Controls : Prop :=
  (FrameSatisfies .S4 ascending ∧ NecessaryIf ascending G false ∧
    Dia ascending G false ∧ Dia ascending (fun v => ¬ G v) false ∧
    ¬ Box ascending G false ∧ ¬ Box ascending (fun v => ¬ G v) false) ∧
  (FrameSatisfies .S5 universal ∧ ActualConditional universal G false ∧
    ¬ NecessaryIf universal G false ∧ Dia universal G false ∧
    Dia universal (fun v => ¬ G v) false ∧
    ¬ Box universal G false ∧ ¬ Box universal (fun v => ¬ G v) false) ∧
  (Euclidean empty ∧ ¬ Serial empty ∧ NecessaryIf empty G false ∧
    Box empty G false ∧ Box empty (fun v => ¬ G v) false ∧
    ¬ Dia empty G false ∧ ¬ Dia empty (fun v => ¬ G v) false) ∧
  (FrameSatisfies .S5 identity ∧ (∀ w, NecessaryIf identity G w) ∧
    Box identity G true ∧ Box identity (fun v => ¬ G v) false ∧
    ¬ (∀ w, G w) ∧ ¬ (∀ w, ¬ G w)) ∧
  (NecessaryIf universal (fun _ => True) false ∧
    Dia universal (fun _ => True) false ∧
    ¬ Dia universal (fun _ => ¬ True) false) ∧
  (NecessaryIf universal (fun _ => False) false ∧
    Dia universal (fun _ => ¬ False) false ∧
    ¬ Dia universal (fun _ => False) false)
end TruthCore.Modal.NecessaryIfExistent
