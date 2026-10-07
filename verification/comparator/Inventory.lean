import VerificationAll
import Lean

/-! Enumerate public theorems by their defining module, including our additions to CSLib.
The reference inventory, not a candidate-provided target list, determines the acceptance gate. -/

open Lean in
run_elab do
  let env ← getEnv
  let mut publicNames : Array String := #[]
  let mut proofs : Array String := #[]
  for (name, info) in env.constants.toList do
    if info.isTheorem then
      if let some index := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[index.toNat]!
        if owner == `Frontier || (`Frontier).isPrefixOf owner then
          proofs := proofs.push name.toString
          if !isPrivateName name && !name.isInternal then
            publicNames := publicNames.push name.toString
  let result := Lean.Json.mkObj [
    ("public", Lean.toJson (publicNames.qsort (· < ·))),
    ("proofs", Lean.toJson (proofs.qsort (· < ·)))]
  IO.println ("FRONTIER_THEOREMS=" ++ result.compress)
