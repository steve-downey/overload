-- Tools/Emit.lean                                                    -*-lean-*-
-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
import Overload

/-!
`lake exe emit <dir>` writes one C++ translation unit per case, the
Standard side's (`Overload.Emit.cases`) and the encoding's
(`Overload.Typeclass.Emit.cases`), into `dir`; `scripts/differential.sh`
compiles them.
-/

open Overload.Emit

/-- Every case of both sides. -/
def allCases : List Case := cases ++ Overload.Typeclass.Emit.cases

def main (args : List String) : IO UInt32 := do
  match args with
  | [dir] =>
    IO.FS.createDirAll dir
    for c in allCases do
      let path := System.FilePath.mk dir / s!"{c.name}.cpp"
      IO.FS.writeFile path (render c)
    IO.println s!"emitted {allCases.length} programs into {dir}"
    return 0
  | _ =>
    IO.eprintln "usage: lake exe emit <dir>"
    return 1
