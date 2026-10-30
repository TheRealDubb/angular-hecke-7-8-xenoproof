import Lean
import Lean.Util.FoldConsts

open Lean

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{module := `AngularPhysicalNormTwistNonvanishing}] {} fun env => do
    let target := `OAI.SevenEighths.Angular.PhysicalFinalAssembly.brief_norm_twist_nonzero
    let mut queue : Array Name := #[target]
    let mut seen : NameSet := {}
    let mut axioms : NameSet := {}
    let mut index := 0
    while index < queue.size do
      let n := queue[index]!
      index := index + 1
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | throw <| IO.userError s!"MISSING {n}"
      if ci.isUnsafe || ci.isPartial then
        throw <| IO.userError s!"Unsafe or partial proof dependency: {n}"
      match ci with
      | .axiomInfo _ =>
        axioms := axioms.insert n
        IO.println s!"AXIOM {n}"
        unless #[`propext, `Classical.choice, `Quot.sound].contains n do
          throw <| IO.userError s!"Unexpected axiom: {n}"
      | _ => pure ()
      for dep in ci.getUsedConstantsAsSet do
        if !seen.contains dep then queue := queue.push dep
    unless axioms.size == 3 do throw <| IO.userError "Unexpected axiom count"
    IO.println s!"CENSUS constants={seen.size}, unsafe=0, partial=0, axioms={axioms.size}"
    IO.println "PUBLIC CLOSURE CENSUS PASSED"
