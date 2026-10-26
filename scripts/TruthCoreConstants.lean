/-
List every declaration of the `TruthCore` library for the scoped NanoDa check.

Usage, after `lake build`:

    lake env lean --run scripts/TruthCoreConstants.lean <ROOT-MODULE>

The tool imports `<ROOT-MODULE>` (normally `TruthCore`) and prints, one per
line, every constant whose defining module lies under the same root namespace
(`TruthCore.*`), skipping internal names exactly as `lean4export` does when it
is given no constant list. `scripts/verify-library.sh` passes the list to
`lean4export`, which exports these constants together with every declaration
they depend on (from Mathlib or Lean core), and NanoDa checks that export.

Each name is printed in the escaped form that `lean4export` parses back. The
tool fails if a name does not round-trip, so the exporter can never receive a
name it would mis-read.
-/
import Lean

open Lean

def main (args : List String) : IO UInt32 := do
  let [root] := args
    | IO.eprintln "usage: lean --run scripts/TruthCoreConstants.lean <ROOT-MODULE>"; return 2
  initSearchPath (← findSysroot)
  let rootName := root.toName
  let env ← importModules #[{ module := rootName }] {}
  let package := rootName.getRoot
  let mut names : Array String := #[]
  for (c, _) in env.constants.toList do
    if c.isInternal then continue
    let some idx := env.getModuleIdxFor? c | continue
    let some mod := env.header.moduleNames[idx.toNat]? | continue
    if mod.getRoot != package then continue
    let printed := toString c
    unless Syntax.decodeNameLit ("`" ++ printed) == some c do
      IO.eprintln s!"constant name does not round-trip through lean4export's parser: {printed}"
      return 1
    names := names.push printed
  if names.isEmpty then
    IO.eprintln s!"no constants found under {package}"
    return 1
  for name in names.qsort (· < ·) do
    IO.println name
  return 0
