module

import Lean

/-! Bounded, read-only strict-correspondence diagnostic.
Run after Challenge and Solution have been built:
  lake env lean --run scripts/inspect_correspondence.lean [comparator.json]
Imports the modules into separate environments; uses the same hole selection
rules as compare_constants.lean; inventories every Challenge-origin constant.
Never renders complete expressions. Unequal expression fields are traversed
in function/type-first preorder, emitting at most 12 structural leaf mismatches,
with 200000 visited nodes and depth 2048 as explicit diagnostic limits.
Binder metadata is shown for context; Expr BEq uses alpha equivalence and ignores
binder annotations, so annotations alone are not treated as comparator errors.
All configured definition holes emit both actual reducibility hints, even when
allowed matching succeeds. No environment or declaration is mutated.
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

private def clipped (s : String) (limit : Nat := 240) : String :=
  if s.length ≤ limit then s else String.ofList (s.toList.take limit) ++ "…"

private def levelSummary : Nat → Level → String
  | 0, _ => "…"
  | _ + 1, .zero => "0"
  | fuel + 1, .succ u => "succ(" ++ levelSummary fuel u ++ ")"
  | fuel + 1, .max u v => "max(" ++ levelSummary fuel u ++ "," ++ levelSummary fuel v ++ ")"
  | fuel + 1, .imax u v => "imax(" ++ levelSummary fuel u ++ "," ++ levelSummary fuel v ++ ")"
  | _ + 1, .param n => "param:" ++ clipped n.toString
  | _ + 1, .mvar n => "mvar:" ++ clipped n.name.toString

private def levelsJson (us : List Level) : Json :=
  Json.arr ((us.take 16).toArray.map (fun u => toJson (clipped (levelSummary 8 u))))

private def headSummary : Nat → Expr → String
  | 0, _ => "…"
  | fuel + 1, .app f _ => headSummary fuel f
  | fuel + 1, .mdata _ e => headSummary fuel e
  | _ + 1, .const n _ => clipped n.toString
  | _ + 1, e => e.ctorName

private def dataSummary : DataValue → Json
  | .ofString s => Json.mkObj [("kind", toJson "string"), ("value", toJson (clipped s))]
  | .ofBool b => Json.mkObj [("kind", toJson "bool"), ("value", toJson b)]
  | .ofName n => Json.mkObj [("kind", toJson "name"), ("value", toJson (clipped n.toString))]
  | .ofNat n => Json.mkObj [("kind", toJson "nat"), ("value", toJson (clipped (toString n)))]
  | .ofInt n => Json.mkObj [("kind", toJson "int"), ("value", toJson (clipped (toString n)))]
  | .ofSyntax stx => Json.mkObj [("kind", toJson "syntax"),
      ("syntax_kind", toJson (clipped stx.getKind.toString))]

private def nodeSummary (e : Expr) : Json :=
  let extra := match e with
    | .bvar i => [("index", toJson i)]
    | .fvar i => [("id", toJson (clipped i.name.toString))]
    | .mvar i => [("id", toJson (clipped i.name.toString))]
    | .sort u => [("level", toJson (clipped (levelSummary 8 u)))]
    | .const n us => [("constant", toJson (clipped n.toString)), ("levels", levelsJson us)]
    | .app .. => [("head", toJson (headSummary 24 e))]
    | .lam n _ _ bi | .forallE n _ _ bi =>
        [("binder_name", toJson (clipped n.toString)), ("binder_info", toJson (reprStr bi))]
    | .letE n _ _ _ nondep => [("binder_name", toJson (clipped n.toString)), ("nondependent", toJson nondep)]
    | .lit (.natVal n) => [("literal", toJson (clipped (toString n)))]
    | .lit (.strVal v) => [("literal", toJson (clipped v)), ("string_length", toJson v.length)]
    | .mdata md _ => [("metadata_entries", Json.arr ((md.entries.take 16).toArray.map (fun (key, value) =>
        Json.mkObj [("key", toJson (clipped key.toString)), ("value", dataSummary value)])))]
    | .proj n i _ => [("structure", toJson (clipped n.toString)), ("index", toJson i)]
  Json.mkObj ([("node", toJson e.ctorName)] ++ extra)

private def exprFields (c : ConstantInfo) : List (String × Expr) :=
  ("type", c.type) :: match c with
    | .defnInfo v => [("value", v.value)]
    | .thmInfo v => [("value", v.value)]
    | .opaqueInfo v => [("value", v.value)]
    | .recInfo v => v.rules.zipIdx |>.map (fun (r, i) => (s!"rules[{i}].rhs", r.rhs))
    | _ => []

private def fields (c : ConstantInfo) : List (String × Json) := Id.run do
  let common := [
    ("kind", toJson (kindName c)),
    ("name", toJson (toString c.name)),
    ("levelParams", namesJson c.levelParams)]
  let extra := match c with
    | .defnInfo v => [
        ("hints", hintsJson v.hints),
        ("safety", toJson (reprStr v.safety)), ("all", namesJson v.all)]
    | .thmInfo v => [("all", namesJson v.all)]
    | .opaqueInfo v => [
        ("isUnsafe", toJson v.isUnsafe),
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
          ("ctor", toJson (toString r.ctor)), ("nfields", toJson r.nfields)]))]
    | .quotInfo v => [("quotKind", toJson (match v.kind with
        | .type => "type" | .ctor => "constructor" | .lift => "lift" | .ind => "induction"))]
  return common ++ extra

private def emit (xs : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj xs).compress

private def inspectExpr (n : Name) (field : String) (c s : Expr) : IO Unit := do
  let mut pending := [("root", 0, c, s)]
  let mut visited := 0
  let mut differences := 0
  let mut depthLimited := false
  while !pending.isEmpty && visited < 200000 && differences < 12 do
    let (path, depth, a, b) := pending.head!
    pending := pending.tail!
    visited := visited + 1
    if a == b then continue
    let children : List (String × Expr × Expr) := match a, b with
      | .app af aa, .app bf ba => [("fn", af, bf), ("arg", aa, ba)]
      | .lam _ aType ab _, .lam _ bType bb _ => [("binder_type", aType, bType), ("body", ab, bb)]
      | .forallE _ aType ab _, .forallE _ bType bb _ => [("binder_type", aType, bType), ("body", ab, bb)]
      | .letE _ aType av ab _, .letE _ bType bv bb _ => [("type", aType, bType), ("value", av, bv), ("body", ab, bb)]
      | .mdata _ ae, .mdata _ be => [("body", ae, be)]
      | .proj an ai ae, .proj bn bi be => if an == bn && ai == bi then [("body", ae, be)] else []
      | _, _ => []
    let children := children.filter (fun (_, ca, sa) => ca != sa)
    if children.isEmpty || depth ≥ 2048 then
      depthLimited := depthLimited || depth ≥ 2048
      differences := differences + 1
      emit [("event", toJson "expr_difference"), ("name", toJson n.toString),
        ("field", toJson field), ("path", toJson (clipped path 4096)),
        ("depth", toJson depth), ("challenge", nodeSummary a), ("solution", nodeSummary b)]
    else
      pending := (children.map fun (part, ca, sa) => (path ++ "." ++ part, depth + 1, ca, sa)) ++ pending
  emit [("event", toJson "expr_scan"), ("name", toJson n.toString),
    ("field", toJson field), ("visited", toJson visited), ("reported", toJson differences),
    ("complete", toJson (pending.isEmpty && !depthLimited)),
    ("node_budget", toJson (200000 : Nat)), ("difference_budget", toJson (12 : Nat)),
    ("depth_budget", toJson (2048 : Nat)),
    ("challenge_root", nodeSummary c), ("solution_root", nodeSummary s)]

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
  if namedDefinition then
    emit [("event", toJson "definition_hole_hints"), ("name", toJson n.toString),
      ("allowed_match", toJson same),
      ("challenge", match c with | .defnInfo v => hintsJson v.hints | _ => Json.null),
      ("solution", match s with | .defnInfo v => hintsJson v.hints | _ => Json.null)]
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
    let ce := exprFields c
    let se := exprFields s
    for (field, cv) in ce do
      if namedTheorem && field != "type" then continue
      if namedDefinition && field != "type" then continue
      match se.lookup field with
      | some sv =>
        if cv != sv then
          explained := true
          inspectExpr n field cv sv
      | none =>
        explained := true
        emit [("event", toJson "missing_expression_field"), ("name", toJson n.toString),
          ("field", toJson field), ("challenge", nodeSummary cv)]
    if !explained then
      emit [("event", toJson "unexplained_raw_mismatch"), ("name", toJson n.toString),
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
