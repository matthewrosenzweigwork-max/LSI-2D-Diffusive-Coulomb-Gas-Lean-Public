module

import Lean

/-! Read-only diagnostic for strict Challenge/Solution constant correspondence.
Run from a built project with:
  lake env lean --run scripts/compare_constants.lean [comparator.json]
The optional positional argument selects a Comparator config path. Module names
and theorem/definition holes come from that JSON; no project names are hardcoded.
Output is JSON Lines; mismatches are findings, not a nonzero diagnostic exit.
Challenge and Solution are imported into separate environments. No declarations
are changed. Named holes use Lake.Check's comparison boundary; every other
Challenge-origin declaration is compared in full, including generated helpers.
The complete inventory is diagnostic and is not a dependency-closure verdict.
-/

open Lean

private def namesJson (ns : List Name) : Json :=
  toJson (ns.map toString)

private def hintsJson : ReducibilityHints → Json
  | .opaque => Json.mkObj [("kind", toJson "opaque")]
  | .abbrev => Json.mkObj [("kind", toJson "abbrev")]
  | .regular h => Json.mkObj [("kind", toJson "regular"), ("height", toJson h.toNat)]

private def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def fields (c : ConstantInfo) : List (String × Json) := Id.run do
  let common := [
    ("kind", toJson (kindName c)),
    ("name", toJson (toString c.name)),
    ("levelParams", namesJson c.levelParams),
    ("type", toJson (reprStr c.type))]
  let extra := match c with
    | .defnInfo v => [
        ("value", toJson (reprStr v.value)), ("hints", hintsJson v.hints),
        ("safety", toJson (reprStr v.safety)), ("all", namesJson v.all)]
    | .thmInfo v => [("value", toJson (reprStr v.value)), ("all", namesJson v.all)]
    | .opaqueInfo v => [
        ("value", toJson (reprStr v.value)), ("isUnsafe", toJson v.isUnsafe),
        ("all", namesJson v.all)]
    | .axiomInfo v => [("isUnsafe", toJson v.isUnsafe)]
    | .inductInfo v => [
        ("numParams", toJson v.numParams), ("numIndices", toJson v.numIndices),
        ("all", namesJson v.all), ("ctors", namesJson v.ctors),
        ("numNested", toJson v.numNested), ("isRec", toJson v.isRec),
        ("isUnsafe", toJson v.isUnsafe), ("isReflexive", toJson v.isReflexive)]
    | .ctorInfo v => [
        ("induct", toJson (toString v.induct)), ("cidx", toJson v.cidx),
        ("numParams", toJson v.numParams), ("numFields", toJson v.numFields),
        ("isUnsafe", toJson v.isUnsafe)]
    | .recInfo v => [
        ("all", namesJson v.all), ("numParams", toJson v.numParams),
        ("numIndices", toJson v.numIndices), ("numMotives", toJson v.numMotives),
        ("numMinors", toJson v.numMinors), ("k", toJson v.k),
        ("isUnsafe", toJson v.isUnsafe),
        ("rules", Json.arr (v.rules.toArray.map fun r => Json.mkObj [
          ("ctor", toJson (toString r.ctor)), ("nfields", toJson r.nfields),
          ("rhs", toJson (reprStr r.rhs))]))]
    | .quotInfo v => [("quotKind", toJson (match v.kind with
        | .type => "type" | .ctor => "constructor" | .lift => "lift" | .ind => "induction"))]
  return common ++ extra

private def emit (xs : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj xs).compress

private def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString (env.header.moduleNames[i.toNat]!)
  | none => "<unrecorded>"

private def compareOne (challenge solution : Environment) (n : Name)
    (namedTheorem namedDefinition : Bool) : IO Bool := do
  let some c := challenge.find? n
    | emit [("event", toJson "missing_challenge"), ("name", toJson (toString n))]; return false
  let some s := solution.find? n
    | emit [("event", toJson "missing_solution"), ("name", toJson (toString n)),
        ("challenge_module", toJson (moduleOf challenge n))]; return false
  -- Match Lake.Check.compareAt and definitionHoleMatches. Theorem holes
  -- require theorem/theorem or axiom/axiom with matching ConstantVal. Definition
  -- holes require matching ConstantVal and safety, but not matching values.
  let same := if namedTheorem then
      match c, s with
      | .thmInfo cc, .thmInfo sc => cc.toConstantVal == sc.toConstantVal
      | .axiomInfo cc, .axiomInfo sc => cc.toConstantVal == sc.toConstantVal
      | _, _ => false
    else if namedDefinition then
      match c, s with
      | .defnInfo cc, .defnInfo sc =>
        cc.toConstantVal == sc.toConstantVal && cc.safety == sc.safety
      | _, _ => false
    else c == s
  emit [("event", toJson "constant"), ("name", toJson (toString n)),
    ("equal", toJson same), ("named_theorem", toJson namedTheorem),
    ("named_definition", toJson namedDefinition),
    ("challenge_module", toJson (moduleOf challenge n)),
    ("solution_module", toJson (moduleOf solution n))]
  if !same then
    let cf := fields c
    let sf := fields s
    let mut keys := cf.map Prod.fst
    for (k, _) in sf do
      if !keys.contains k then keys := keys ++ [k]
    let mut explained := false
    for k in keys do
      if namedTheorem && !(k == "kind" || k == "name" || k == "levelParams" || k == "type") then
        continue
      if namedDefinition && !(k == "kind" || k == "name" || k == "levelParams" ||
          k == "type" || k == "safety") then
        continue
      let cv := cf.lookup k
      let sv := sf.lookup k
      if cv != sv then
        explained := true
        emit [("event", toJson "field_mismatch"), ("name", toJson (toString n)),
          ("field", toJson k), ("challenge", cv.getD Json.null),
          ("solution", sv.getD Json.null)]
    if !explained then
      emit [("event", toJson "unexplained_raw_mismatch"), ("name", toJson (toString n)),
        ("challenge", Json.mkObj cf), ("solution", Json.mkObj sf)]
  return same

private def configField (config : Json) (α : Type) [FromJson α]
    (field : String) : IO α :=
  match config.getObjValAs? α field with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"Comparator field {field}: {error}")

public def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let configPath := args[0]?.getD "comparator.json"
  let config ← match Json.parse (← IO.FS.readFile configPath) with
    | .ok config => pure config
    | .error error => throw (IO.userError s!"Comparator JSON: {error}")
  let challengeModule := (← configField config String "challenge_module").toName
  let solutionModule := (← configField config String "solution_module").toName
  let theoremNames := (← configField config (Array String) "theorem_names").map String.toName
  let definitionNames := (← configField config (Array String) "definition_names").map String.toName
  if theoremNames.any definitionNames.contains then
    throw (IO.userError "A declaration cannot be both a theorem and definition hole")
  let challenge ← importModules #[{ module := challengeModule }] {}
  let solution ← importModules #[{ module := solutionModule }] {}
  emit [("event", toJson "environments"),
    ("config", toJson configPath),
    ("challenge", toJson (toString challengeModule)),
    ("solution", toJson (toString solutionModule)),
    ("theorem_names", namesJson theoremNames.toList),
    ("definition_names", namesJson definitionNames.toList),
    ("separate_environments", toJson true)]
  let mut names := theoremNames ++ definitionNames
  -- Include every generated field, constructor, recursor, instance and helper
  -- originating in Challenge, not only the configured holes.
  let some challengeIdx := challenge.getModuleIdx? challengeModule
    | throw (IO.userError s!"No module index for {challengeModule}")
  for (n, _) in challenge.constants.toList do
    if challenge.getModuleIdxFor? n == some challengeIdx && !names.contains n then
      names := names.push n
  names := names.qsort (fun a b => a.toString < b.toString)
  let mut equal := 0
  let mut different := 0
  for n in names do
    if ← compareOne challenge solution n (theoremNames.contains n) (definitionNames.contains n) then
      equal := equal + 1
    else different := different + 1
  emit [("event", toJson "summary"), ("checked", toJson names.size),
    ("equal", toJson equal), ("different_or_missing", toJson different),
    ("configured_theorems", toJson theoremNames.size),
    ("configured_definitions", toJson definitionNames.size)]
