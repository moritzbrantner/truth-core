/-
Emit the binder structure of advertised result theorems as JSON (#162).

Usage, after `lake build`:

    lake env lean --run scripts/BindTypes.lean <input.json>

`<input.json>` is `{"modules": [...], "theorems": [...]}`. The tool imports the
modules, reads each theorem's type with `forallTelescope` (no reduction), and
prints one JSON object per theorem: every binder with its name, whether its
type lives in `Prop` (a propositional hypothesis) or not (a type or vocabulary
parameter), and the head constant of that type; then the same for the result
type. `scripts/corpus.py bind-check` compares this with the corpus records.

Head constants are read syntactically (`getAppFn` after stripping metadata).
Nothing is unfolded, so a `…Reading` definition applied to arguments reports
that definition. Logical wrappers the corpus may use around a declaration are
peeled and listed separately: `¬` (`Not`) and `∃` (`Exists`).
-/
import Lean

open Lean Meta

/-- Strip metadata and return the head constant of `e`, if any. -/
def headConst? (e : Expr) : Option Name :=
  match e.consumeMData.getAppFn.consumeMData with
  | .const n _ => some n
  | _ => none

/-- Peel `Not` and `Exists` wrappers. Returns the wrappers (outermost first)
and the head constant of the innermost proposition. -/
partial def peel (e : Expr) (acc : Array String) : MetaM (Array String × Option Name) := do
  let e := e.consumeMData
  if e.isAppOfArity ``Not 1 then
    peel e.appArg! (acc.push "Not")
  else if e.isAppOfArity ``Exists 2 then
    match e.appArg!.consumeMData with
    | .lam n ty body bi =>
      withLocalDecl n bi ty fun x => peel (body.instantiate1 x) (acc.push "Exists")
    | _ => return (acc.push "Exists", none)
  else
    return (acc, headConst? e)

def nameJson : Option Name → Json
  | some n => Json.str n.toString
  | none => Json.null

/-- Describe one type: its sort class, raw head, peeled wrappers and core head. -/
def describeType (ty : Expr) : MetaM Json := do
  let ty ← instantiateMVars ty
  let sort ← whnf (← inferType ty)
  let isProp := sort.isProp
  let (wrappers, core) ← peel ty #[]
  let pp ← ppExpr ty
  return Json.mkObj [
    ("prop", Json.bool isProp),
    ("head", nameJson (headConst? ty)),
    ("wrappers", toJson wrappers),
    ("core_head", nameJson core),
    ("type", Json.str (toString pp))
  ]

def describeTheorem (thm : Name) : MetaM Json := do
  let some info := (← getEnv).find? thm
    | return Json.mkObj [("theorem", Json.str thm.toString), ("error", Json.str "unknown constant")]
  forallTelescope info.type fun xs body => do
    let mut binders : Array Json := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      let d ← describeType decl.type
      binders := binders.push (d.mergeObj (Json.mkObj [("name", Json.str decl.userName.toString)]))
    let result ← describeType body
    return Json.mkObj [
      ("theorem", Json.str thm.toString),
      ("binders", Json.arr binders),
      ("result", result)
    ]

unsafe def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: lean --run scripts/BindTypes.lean <input.json>"; return 2
  let input ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let modules ← IO.ofExcept (input.getObjValAs? (Array String) "modules")
  let theorems ← IO.ofExcept (input.getObjValAs? (Array String) "theorems")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map fun m => { module := m.toName }) {}
    (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "<bind-types>", fileMap := default, maxHeartbeats := 0 }
  let state : Core.State := { env }
  let (out, _) ← (MetaM.run' (theorems.mapM fun t => describeTheorem t.toName)).toIO ctx state
  IO.println (Json.arr out).compress
  return 0
