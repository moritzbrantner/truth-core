import Lean
/-
Throwaway Lean trial of bridge candidates (#415). `scripts/bridge_trial.py`
prepends `import` lines for the declarations' modules (and Aesop), then
appends one command per candidate:

  #bridge_try "label" Target from Premise₁ Premise₂

The command opens the target declaration's binders, instantiates each
premise's binders by an in-scope binder of the same name and definitionally
equal type (an instance binder by type alone, or by instance synthesis), and
universally quantifies any premise binder it cannot match (reported as
`generalized`: a stronger reading than the premise). It then attempts the goal

  ∀ target-binders, premise₁ → premise₂ → Target target-binders

after `intros` and unfolding exactly the named statement declarations, with
each automation tactic separately, under the ambient `maxHeartbeats`. Two
controls run on the same instantiation: the target alone (no premises) and
`False` from the premises (vacuity). A closed goal is kernel-checked with
`addDecl` on an auxiliary name that is not exported, and its axioms are
reported: `grind`, `aesop` and `simp_all` may use classical reasoning, which a
zero-axiom (non-Mathlib) result may not.

Every outcome is a CANDIDATE: a closed goal shows only that these Lean
declarations, under this instantiation, compose. It says nothing about the
fidelity of either reading (AGENTS.md invariants 6 and 16), and a failed
search is not a refutation. Results are printed as `BRIDGE-JSON` info lines.
-/
open Lean Elab Command Term Meta

namespace BridgeTrial

/-- Apply `e` to binders found in `xs` by name and type; quantify the rest. -/
partial def instantiate (xs : Array Expr) (e : Expr) : MetaM (Expr × Array String) := do
  let ty ← instantiateMVars (← inferType e)
  match ty with
  | .forallE n d _ bi =>
    for x in xs do
      -- Instance binders carry hygienic names: match them by type alone.
      if bi.isInstImplicit || (← x.fvarId!.getUserName) == n then
        if ← isDefEq (← inferType x) d then
          return ← instantiate xs (mkApp e x)
    if bi.isInstImplicit then
      if let some inst ← (try synthInstance? d catch _ => pure none) then
        return ← instantiate xs (mkApp e inst)
    withLocalDecl n bi d fun y => do
      let (body, generalized) ← instantiate xs (mkApp e y)
      return (← mkForallFVars #[y] body, generalized.push n.toString)
  | _ => return (e, #[])

def tactics (unfold : Array Ident) : TermElabM (Array (String × Syntax)) := do
  -- One `try unfold` per name: `unfold A B at *` fails as a whole when one
  -- of them does not occur, which would leave the others folded.
  let mut pre ← `(tactic| intros)
  for name in unfold do
    pre ← `(tactic| ($pre; try unfold $name:ident at *))
  return #[
    ("assumption", ← `(tactic| ($pre; assumption))),
    ("solve_by_elim", ← `(tactic| ($pre; solve_by_elim))),
    ("simp_all", ← `(tactic| ($pre; simp_all; done))),
    ("aesop", ← `(tactic| ($pre; aesop))),
    ("grind", ← `(tactic| ($pre; grind)))]

/-- The first tactic that closes `goal` with a kernel-checked proof, and the
axioms that proof uses. -/
def attempt (goal : Expr) (tacs : Array (String × Syntax)) :
    TermElabM (Option (String × Array Name)) := do
  let goal ← instantiateMVars goal
  let goal ← levelMVarToParam goal
  let levelParams := (collectLevelParams {} goal).params.toList
  for (name, tac) in tacs do
    let saved ← saveState
    let closed ← tryCatchRuntimeEx (do
        let mvar ← mkFreshExprMVar goal
        let remaining ← Tactic.run mvar.mvarId! (Tactic.evalTactic tac)
        synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars mvar
        if !remaining.isEmpty || proof.hasMVar || proof.hasSorry then
          return none
        let aux ← mkFreshUserName `_bridgeTrial
        addDecl (.thmDecl { name := aux, levelParams, type := goal, value := proof })
        return some (← collectAxioms aux))
      (fun _ => pure none)
    saved.restore (restoreInfo := true)
    if let some axioms := closed then
      return some (name, axioms.qsort Name.lt)
  return none

def trial (target : Name) (premises : Array Name) : TermElabM Json := do
  let some info := (← getEnv).find? target
    | return Json.mkObj [("error", Json.str s!"unknown target {target}")]
  let targetConst := Lean.mkConst target (info.levelParams.map Level.param)
  forallTelescope info.type fun xs body => do
    unless body.isProp do
      return Json.mkObj [("error", Json.str "target declaration is not a Prop-valued family")]
    let conclusion := mkAppN targetConst xs
    let mut hyps := #[]
    let mut generalized := #[]
    for premise in premises do
      let (hyp, gen) ← instantiate xs (← mkConstWithFreshMVarLevels premise)
      unless (← inferType hyp).isProp do
        return Json.mkObj [("error", Json.str s!"premise {premise} is not a Prop-valued family")]
      hyps := hyps.push hyp
      generalized := generalized ++ gen.map (s!"{premise}.{·}")
    let unfold := (premises.push target).map mkIdent
    let tacs ← tactics unfold
    let close (concl : Expr) (withHyps : Bool) : TermElabM (Option (String × Array Name)) := do
      let body ← (if withHyps then hyps else #[]).foldrM (fun h acc => mkArrow h acc) concl
      attempt (← mkForallFVars xs body) tacs
    let alone ← close conclusion false
    let vacuous ← close (Lean.mkConst ``False) true
    let closed ← close conclusion true
    let goalText ← ppExpr (← mkForallFVars xs (← hyps.foldrM (fun h acc => mkArrow h acc) conclusion))
    return Json.mkObj [
      ("closed_by", (closed.map (Json.str ·.1)).getD Json.null),
      ("axioms", (closed.map fun c => Json.arr (c.2.map (Json.str ·.toString))).getD Json.null),
      ("target_alone_closed_by", (alone.map (Json.str ·.1)).getD Json.null),
      ("premises_refuted_by", (vacuous.map (Json.str ·.1)).getD Json.null),
      ("generalized", Json.arr (generalized.map Json.str)),
      ("goal", Json.str (toString goalText))]

syntax (name := bridgeTry) "#bridge_try " str ident " from " ident* : command

@[command_elab bridgeTry] def elabBridgeTry : CommandElab := fun stx => do
  let label := stx[1].isStrLit?.getD ""
  let target := stx[2].getId
  let premises := stx[4].getArgs.map (·.getId)
  let result ← liftTermElabM do
    try trial target premises
    catch e => return Json.mkObj [("error", Json.str (← e.toMessageData.toString))]
  logInfo m!"BRIDGE-JSON {(result.setObjVal! "label" (Json.str label)).compress}"

end BridgeTrial
