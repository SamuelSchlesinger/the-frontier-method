import Comparator.Driver

/-!
Invoke upstream Comparator on exports from two isolated projects. The upstream command-line
driver assumes both modules belong to one project; only that orchestration is replaced here.
Statement/definition comparison, axiom checking, and kernel replay are upstream operations.

No candidate `.olean` is imported into this process. `--run` uses the imported `main`, so the
harness instead sets `FRONTIER_COMPARATOR_JOB` and elaborates this trusted file with `lean`.
-/

#eval show IO Unit from do
  if let some directory ← IO.getEnv "FRONTIER_COMPARATOR_JOB" then
    let directory : System.FilePath := directory
    let configText ← IO.FS.readFile (directory / "config.json")
    let config : Comparator.Config ← IO.ofExcept <|
      Lean.fromJson? (← IO.ofExcept <| Lean.Json.parse configText)
    if config.theorem_names.isEmpty then
      throw <| IO.userError "Refusing an empty theorem selection"
    let expectedAxioms := #["propext", "Quot.sound", "Classical.choice"]
    if config.permitted_axioms != expectedAxioms then
      throw <| IO.userError "The permitted axiom policy has changed"
    if !(config.definition_names.getD #[]).isEmpty then
      throw <| IO.userError "Definition holes are not permitted"
    let challenge ← IO.FS.readFile (directory / "reference.ndjson")
    let solution ← IO.FS.readFile (directory / "candidate.ndjson")
    let rootsText ← IO.FS.readFile (directory / "candidate_roots.json")
    let roots : Array String ← IO.ofExcept <|
      Lean.fromJson? (← IO.ofExcept <| Lean.Json.parse rootsText)
    if !config.theorem_names.all roots.contains then
      throw <| IO.userError "The proof inventory omits a public theorem"
    -- Private and generated theorem statements may change in a proof refactor, but their
    -- proof terms must still use only the permitted axioms and pass the kernel replay.
    let parsed ← Export.parseStream (← Comparator.stringStream solution)
    IO.ofExcept <| Comparator.checkAxioms parsed (roots.map String.toName) #[]
      (expectedAxioms.map String.toName)
    Comparator.M.run (Comparator.verifyMatch challenge solution) config
    IO.println s!"Comparator accepted {config.theorem_names.size} theorem statements and proofs."
