/-
List every declaration of the `TruthCore` library for the scoped NanoDa check.

Usage, after `lake build`:

    lake env lean --run scripts/TruthCoreConstants.lean <ROOT-MODULE> [<MODULES-FILE>]

The tool imports `<ROOT-MODULE>` (normally `TruthCore`) and prints, one per
line, every constant whose defining module lies under the same root namespace
(`TruthCore.*`), skipping internal names exactly as `lean4export` does when it
is given no constant list. `scripts/verify-library.sh` passes the list to
`lean4export`, which exports these constants together with every declaration
they depend on (from Mathlib or Lean core), and NanoDa checks that export.

With `<MODULES-FILE>` (one module name per line), it prints only the constants
defined in those modules; an empty result is then not an error. On a pull
request CI passes the modules whose build output the change can affect
(`scripts/affected_results.py nanoda-modules`). A listed module that
`<ROOT-MODULE>` does not import (a Challenge module, a deleted module) has no
constants here and is reported on standard error.

Each name is printed in the escaped form that `lean4export` parses back. The
tool fails if a name does not round-trip, so the exporter can never receive a
name it would mis-read.
-/
import Lean

open Lean

def main (args : List String) : IO UInt32 := do
  let (root, modulesFile?) ← match args with
    | [root] => pure (root, none)
    | [root, file] => pure (root, some file)
    | _ =>
      IO.eprintln "usage: lean --run scripts/TruthCoreConstants.lean <ROOT-MODULE> [<MODULES-FILE>]"
      return 2
  let selected? : Option NameSet ← modulesFile?.mapM fun file => do
    let lines ← IO.FS.lines file
    return lines.foldl (init := {}) fun set line =>
      let line := line.trimAscii.toString
      if line.isEmpty then set else set.insert line.toName
  initSearchPath (← findSysroot)
  let rootName := root.toName
  let env ← importModules #[{ module := rootName }] {}
  let package := rootName.getRoot
  if let some selected := selected? then
    let imported := env.header.moduleNames.foldl (init := ({} : NameSet)) fun set m => set.insert m
    for m in selected.toList do
      unless imported.contains m do
        IO.eprintln s!"{root} does not import listed module {m}; it contributes no constants"
  let mut names : Array String := #[]
  for (c, _) in env.constants.toList do
    if c.isInternal then continue
    let some idx := env.getModuleIdxFor? c | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    if mod.getRoot != package then continue
    if let some selected := selected? then
      unless selected.contains mod do continue
    let printed := toString c
    unless Syntax.decodeNameLit ("`" ++ printed) == some c do
      IO.eprintln s!"constant name does not round-trip through lean4export's parser: {printed}"
      return 1
    names := names.push printed
  if names.isEmpty && selected?.isNone then
    IO.eprintln s!"no constants found under {package}"
    return 1
  for name in names.qsort (· < ·) do
    IO.println name
  return 0
