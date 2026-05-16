-- import Lean

-- /-!
--   This file defines two attributes, `@[pkt_type_val]` and `@[gen_coder]`,
--   which work together to automatically generate encoder and decoder functions
--   for an inductive type based on integer values assigned to each constructor.

--   This version is updated to be more robust against Lean 4 API version changes.
-- -/
-- namespace AttrCodeGen

-- open Lean Elab Command Term Meta

-- /--
--   An environment extension to store the mapping from a declaration `Name`
--   to its assigned `Nat` value. This state is populated by the `@[pkt_type_val]` attribute.
-- -/
-- initialize pktTypeExt : SimplePersistentEnvExtension (Name × Nat) (Array (Name × Nat)) ←
--   registerSimplePersistentEnvExtension {
--     addImportedFn := fun s => s.foldl (· ++ ·) #[]
--     addEntryFn    := Array.push
--   }

-- /--
--   Attribute syntax for `[pkt_type_val n]`, where `n` is a natural number literal.
-- -/
-- syntax (name := pktTypeVal) "pkt_type_val " num : attr

-- /--
--   Implementation of the `pkt_type_val` attribute. It parses the integer and stores
--   the `(declarationName, integerValue)` pair in our `pktTypeExt` environment extension.

--   NOTE: We have removed the check for `AttributeKind` because its enum names (`ctor`,
--   `constructor`) are highly version-dependent and a common source of errors.
--   Validation is now handled entirely within the `gen_coder` attribute.
-- -/
-- initialize registerBuiltinAttribute {
--   name  := `pktTypeVal
--   descr := "Adds an integer value to a declaration for encoding/decoding."
--   add   := fun decl stx _kind => do
--     let val ← match stx with
--       | `(attr| pkt_type_val $n) => pure n.getNat
--       | _ => throwError "invalid [pkt_type_val] attribute syntax"
--     setEnv <| pktTypeExt.addEntry (← getEnv) (decl, val)
-- }

-- /--
--   Attribute `[gen_coder]` to be placed on an inductive type definition.
--   It triggers the automatic generation of `encode` and `decode` functions.
-- -/
-- syntax (name := genCoder) "gen_coder" : attr

-- /--
--   Implementation of the `gen_coder` attribute. It reads the mapping from `pktTypeExt`
--   and generates the corresponding `encode` and `decode` functions.
-- -/
-- initialize registerBuiltinAttribute {
--   name  := `genCoder
--   descr := "Generates encode/decode functions for an inductive type with [pkt_type_val] constructors."
--   add   := fun typeDeclName _stx _kind => do
--     let env ← getEnv
--     let some (ConstantInfo.inductInfo indInfo) := env.find? typeDeclName
--       | throwError "gen_coder attribute can only be applied to inductive types"

--     -- Create a map from Name to Nat for efficient lookup.
--     let allMappings : NameMap Nat := (pktTypeExt.getState env).foldl (init := NameMap.empty)
--       (fun acc (n, v) => acc.insert n v)

--     -- Iterate through the actual constructors of the inductive type and build our mapping.
--     -- This is the primary validation step.
--     let mut typeMappings := #[]
--     for ctorName in indInfo.ctors do
--       match allMappings.find? ctorName with
--       | some val => typeMappings := typeMappings.push (ctorName, val)
--       | none => throwError "Constructor '{ctorName}' of '{typeDeclName}' is missing a [pkt_type_val] attribute."

--     if typeMappings.size != indInfo.numCtors then
--       throwError "Not all constructors of '{typeDeclName}' have a [pkt_type_val] attribute."

--     liftCommandElabM do
--       let typeIdent := mkIdent typeDeclName

--       -- 1. Generate the `encode` function.
--       let encodeFnName := typeDeclName.mkStr "encode"
--       -- Building the match alternatives this way is more robust across Lean versions.
--       let encodeAlts ← typeMappings.mapM fun (ctorName, val) =>
--         `(@matchAltExpr| | $(mkIdent ctorName):ident => $(mkNumLit (toString val)))

--       let encodeFn ← `(
--         @[simp]
--         def $(mkIdent encodeFnName):ident (p : $typeIdent) : Nat :=
--           match p with
--             $matchAlts
--       )
--       elabCommand encodeFn

--       -- 2. Generate the `decode` function.
--       let decodeFnName := typeDeclName.mkStr "decode"
--       let paramIdent := mkIdent `n
--       let mut decodeBody := (← `e(none))
--       for (ctorName, val) in typeMappings.reverse do
--         decodeBody ← `(if $paramIdent:ident == $(mkNumLit (toString val)):num then some $(mkIdent ctorName):ident else $decodeBody)

--       let decodeFn ← `(
--         @[simp]
--         def $(mkIdent decodeFnName):ident ($paramIdent : Nat) : Option $typeIdent :=
--           $decodeBody
--       )
--       elabCommand decodeFn
-- }

-- end AttrCodeGen
