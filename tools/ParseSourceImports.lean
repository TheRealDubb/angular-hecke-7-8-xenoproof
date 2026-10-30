import Lean
open Lean

def main (args : List String) : IO Unit := do
  let rows ← IO.FS.lines args[0]!
  for row in rows do
    let parts := row.splitOn "\t"
    let name := parts[0]!
    let path := parts[1]!
    let source ← IO.FS.readFile path
    let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source path)
    if messages.hasErrors then
      throw <| IO.userError s!"Header parsing failed: {name}"
    let imports := (Lean.Elab.HeaderSyntax.imports header false).map (·.module.toString)
    IO.println <| (Json.mkObj [("module", toJson name), ("imports", toJson imports)]).compress
