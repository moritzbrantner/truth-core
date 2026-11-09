module
public import TruthCore.Modal.NecessaryIfExistent

/-! Conditional analyst profile for the A2 alternate/A10 modal input.
This selects Kripke impossibility of ONE formula at ONE standpoint. It is not
the source gloss "contradicts something necessary": that correspondence remains
open, as do coverage of relevant situations and report-to-truth. No frame law,
actual assent, concrete cause or rigid individual is supplied by a question. -/
@[expose] public section
namespace TruthCore.Modal.PossibleImpossibility
open TruthCore.Isabelle.AFP.GoedelGod (MProp Box Dia)
open TruthCore.Modal.NecessaryIfExistent (ImpossibleExistence)
universe u
/-- Selected affirmative CONTENT, with no report or assent premise hidden in it. -/
def Input {W : Type u} (F : Frame W) (P : MProp W) (w : W) : Prop :=
  Dia F (ImpossibleExistence F P) w → ImpossibleExistence F P w
/-- Necessity of possibility for the SAME formula and standpoint. -/
def Stable {W : Type u} (F : Frame W) (P : MProp W) (w : W) : Prop :=
  Dia F P w → Box F (Dia F P) w
/-- Formula-local double-negation elimination on accessible worlds is enough;
global excluded middle is stronger than this conditional calculation needs. -/
def LocalClassical {W : Type u} (F : Frame W) (P : MProp W) (w : W) : Prop :=
  ∀ v, F.access w v → (¬ ¬ Dia F P v → Dia F P v)
/-- Exact formula-local duality calculation; not a universal frame axiom. -/
def Certificate : Prop :=
  ∀ (W : Type) (F : Frame W) (P : MProp W) (w : W),
    LocalClassical F P w → (Input F P w ↔ Stable F P w)
/-- Nonvacuity with live possibility; formula-scope omission; and no inference
from selected content to an independently supplied assent proposition or from
a free source-gloss interpretation to Kripke impossibility. Bool is a control
carrier only; the definitions and certificate quantify over arbitrary worlds. -/
def Controls : Prop :=
  (Input NecessaryIfExistent.universal (fun _ => True) false ∧
    Dia NecessaryIfExistent.universal (fun _ => True) false ∧
    Stable NecessaryIfExistent.universal (fun _ => True) false) ∧
  (Input NecessaryIfExistent.ascending (fun _ => True) false ∧
    ¬ Input NecessaryIfExistent.ascending (fun v => v = false) false ∧
    ¬ Stable NecessaryIfExistent.ascending (fun v => v = false) false) ∧
  (¬ (∀ assent : Prop,
    Input NecessaryIfExistent.universal (fun _ => True) false → assent)) ∧
  ((fun _ : Bool => True) false ∧
    ¬ ImpossibleExistence NecessaryIfExistent.universal (fun _ => True) false)
end TruthCore.Modal.PossibleImpossibility
