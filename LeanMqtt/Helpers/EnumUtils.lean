import Lean
open Lean Elab Command Term Meta

namespace Mqtt

/-!
# Enum Macros

This module contains macros for simple inductive types (enumerators).

The macros include `enum_with_codec`, which generates tagged enums, and
`valid_variants`, which
-/

/-!
## `enum_with_codec`

`enum_with_codec` creates an inductive type whose variants represent some other
type. The macro automatically generates `encode` and `decode?` functions to this
other type.

**Example usage:**
```lean
-- This also generates functions `MyEnum.encode` and `MyEnum.decode?`:
enum_with_codec MyEnum : UInt8 where
  | a => 0
  | b => 1
```

For an example in the codebase, see `Mqtt.GlobalReasonCode`.
-/

syntax enum_variant := "|" ident "=>" num

/--
A generalized macro to define a simple enum-like inductive type
along with its `encode` and `decode?` codec functions.
-/
def expandEnumWithCodec
    (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
    (name : TSyntax `ident)
    (type : TSyntax `term)
    (variants : Array (TSyntax ``enum_variant)) :
    MacroM (TSyntax `command) := do
  let mut indConstructors : Array (TSyntax ``Lean.Parser.Command.ctor) := #[]
  let mut encArms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut decArms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]

  for v in variants do
    match v with
    | `(enum_variant| | $id:ident => $val:num) =>
      -- Constructor: | ident
      let ctor ← `(Lean.Parser.Command.ctor| | $id:ident)
      indConstructors := indConstructors.push ctor

      -- Encode arm: | .ident => val
      let fullId := mkIdentFrom id (Name.mkSimple id.getId.toString)
      let encArm ← `(Lean.Parser.Term.matchAltExpr| | .$fullId => $val)
      encArms := encArms.push encArm

      -- Decode arm: | val => some .ident
      let decArm ← `(Lean.Parser.Term.matchAltExpr| | $val => some .$fullId)
      decArms := decArms.push decArm
    | _ => Macro.throwError "Invalid variant syntax"

  -- default arm for decode?
  let decDefault ← `(Lean.Parser.Term.matchAltExpr| | _ => none)
  decArms := decArms.push decDefault

  let encodeName := mkIdentFrom name (Name.mkStr name.getId "encode")
  let decodeName := mkIdentFrom name (Name.mkStr name.getId "decode?")

  `(
    $[$doc?:docComment]?
    inductive $name where
      $[$indConstructors:ctor]*
    deriving Repr, DecidableEq, Inhabited

    def $encodeName : $name → $type
      $[$encArms:matchAlt]*

    def $decodeName : $type → Option $name
      $[$decArms:matchAlt]*
  )

macro doc?:(docComment)? "enum_with_codec" name:ident ":" type:term "where" variants:enum_variant* : command => do
  expandEnumWithCodec doc? name type variants

elab doc?:(docComment)? "enum_with_codec?" name:ident ":" type:term "where" variants:enum_variant* : command => do
  let stx ← liftMacroM <| expandEnumWithCodec doc? name type variants
  if stx.raw.isOfKind nullKind then
    for arg in stx.raw.getArgs do
      logInfo m!"{arg}"
  else
    logInfo m!"{stx}"
  elabCommand stx

/-!
## `valid_variants`

`valid_variants` creates a function to validate subsets of an enum to specific tags in `O(1)` time.
This is heavily used to create dependent types that ensure only valid variants are allowed
for a given tag, vastly simplifying pattern matching.

**Example usage:**
```lean
inductive Tag | t1 | t2
inductive Var | v1 | v2 | v3

valid_variants isValidVar : Tag → Var
  | t1 => [v1, v2]
  | t2 => [v3]

def ValidVar (t : Tag) := { v : Var // isValidVar t v }

/- Lean knows this match is exhaustive because `isValidVar .t2` is only true for `.v3`: -/
def handle_t2 (v : ValidVar .t2) : String :=
  match v with
  | ⟨.v3, _⟩ => "Handled v3"
```

For an example in the codebase, see `Mqtt.isValidReasonCode`.
-/

syntax valid_variants_list := "|" ident "=>" "[" ident,* "]"

/--
A generalized macro that creates a validating function for any two simple inductive types,
where one is a tag and the other is the set of possible variants for that tag.
-/
def expandValidVariants
    (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
    (name tag var : TSyntax `ident)
    (lists : Array (TSyntax ``valid_variants_list)) :
    MacroM (TSyntax `command) := do
  let mut arms : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]

  for list in lists do
    match list with
    | `(valid_variants_list| | $t:ident => [ $[$vs:ident],* ]) =>
      for v in vs do
        let fullT := mkIdentFrom t (Name.mkSimple t.getId.toString)
        let fullV := mkIdentFrom v (Name.mkSimple v.getId.toString)
        let arm ← `(Lean.Parser.Term.matchAltExpr| | .$fullT, .$fullV => true)
        arms := arms.push arm
    | _ => Macro.throwError "Invalid list syntax"

  let defaultArm ← `(Lean.Parser.Term.matchAltExpr| | _, _ => false)
  arms := arms.push defaultArm

  `(
    $[$doc?:docComment]?
    def $name (tag_val : $tag) (var_val : $var) : Bool :=
      match tag_val, var_val with
      $[$arms:matchAlt]*
  )

macro doc?:(docComment)? "valid_variants" name:ident ":" tag:ident "→" var:ident lists:valid_variants_list* : command => do
  expandValidVariants doc? name tag var lists

elab doc?:(docComment)? "valid_variants?" name:ident ":" tag:ident "→" var:ident lists:valid_variants_list* : command => do
  let stx ← liftMacroM <| expandValidVariants doc? name tag var lists
  if stx.raw.isOfKind nullKind then
    for arg in stx.raw.getArgs do
      logInfo m!"{arg}"
  else
    logInfo m!"{stx}"
  elabCommand stx

end Mqtt
