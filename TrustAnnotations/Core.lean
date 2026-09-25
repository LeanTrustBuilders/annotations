module

public import Lean

@[expose] public section

/-!
# The generic annotation extension

Every attribute of this package, and every attribute built on it elsewhere, writes its data into
**one** environment extension, as `(attribute, declaration, payload)` entries whose payload is JSON
text.

That is the whole point of the package. A tool that reads annotations out of a compiled project
needs the extension it reads *registered in its own process*: imported extension entries are
matched to registered extensions by name and silently dropped otherwise. If every attribute had an
extension of its own, the reading tool would have to link every attribute package, and a new
attribute would need a new release of the tool for every Lean toolchain. With one generic
extension, the tool links this package once and reads every attribute built on it, including
attributes defined after the tool was released.

## Compatibility

The layout of `Entry` is part of the `.olean` format: a project compiled against one version of
this package is read by a tool linking another. It is therefore fixed — two names and a string —
and anything an attribute needs to evolve goes inside its payload, which carries its own version
when it needs one.

## Importing this module

A file using the module system applies attributes at compile time, so it needs
`meta import TrustAnnotations` (in addition to `import TrustAnnotations` if it also reads the
entries at run time).
-/

namespace TrustAnnotations

open Lean

/-- One annotation.

The layout is part of the `.olean` format; see the module docstring before changing it. -/
structure Entry where
  /-- The attribute that wrote the entry, e.g. `claim`. -/
  attr : Name
  /-- The declaration the entry is about. -/
  decl : Name
  /-- Attribute-specific data, as compact JSON text. `"null"` when the attribute carries none. -/
  payload : String := "null"
deriving Repr, Inhabited, BEq

/-- Every annotation of the current module and of everything it imports, in declaration order. -/
initialize annotationExt : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.flatten
  }

/-- Every annotation visible in `env`, in declaration order. The entry point for tools. -/
def entries (env : Environment) : Array Entry :=
  annotationExt.getState env

/-- The annotations on `decl`. Linear in the number of annotations; group `entries` yourself if you
need this for every declaration. -/
def entriesOn (env : Environment) (decl : Name) : Array Entry :=
  (entries env).filter (·.decl == decl)

/-- The annotations written by the attribute `attr`. -/
def entriesOf (env : Environment) (attr : Name) : Array Entry :=
  (entries env).filter (·.attr == attr)

/-- The payload of an entry, parsed. -/
def Entry.json (e : Entry) : Except String Json :=
  Json.parse e.payload

/-- Whether `info` is a proof, decided from its type rather than from its kind: under the
visibility scope an attribute handler runs in, a theorem of the current module does not always
arrive as a `.thmInfo`. -/
def isProof (info : ConstantInfo) : AttrM Bool :=
  Meta.MetaM.run' (Meta.isProp info.type)

/-- Records an annotation. For implementers of attributes built on this package.

`anchor` must be a declaration of the current module: the entry is written into the module being
elaborated, and a consumer reaches it through that module. -/
def addEntry (entry : Entry) (anchor : Name) : AttrM Unit :=
  modifyEnv fun env => annotationExt.addEntry (asyncDecl := anchor) env entry

/-- What an attribute built on this package computes from its syntax: the payload to record, and
optionally a second declaration the annotation relates to (such as the definition a theorem is an
example of). The related declaration is only used to decide where the entry can be recorded. -/
structure Elaborated where
  payload : Json := Json.null
  related? : Option Name := none

/-- Registers an attribute that records its annotations in the generic extension.

`elaborate` checks the application and computes the payload; it runs after type checking, with the
declaration in the environment. The attribute is global only: an annotation is a claim about the
declaration, not about a section or a namespace. It may be applied only once per declaration. -/
def registerAnnotationAttribute (attrName : Name) (descr : String)
    (elaborate : Name → Syntax → AttrM Elaborated) : IO Unit :=
  registerBuiltinAttribute {
    name := attrName
    descr := descr
    applicationTime := .afterTypeChecking
    add := fun decl stx kind => do
      unless kind == .global do
        throwError "`{attrName}` must be a global attribute: an annotation is a claim about the \
          declaration, not about a section or a namespace"
      let env ← getEnv
      if (entriesOn env decl).any (·.attr == attrName) then
        throwError "`{decl}` already carries `@[{attrName}]`"
      let result ← elaborate decl stx
      -- The entry is written into the module being elaborated. It has to be anchored to a
      -- declaration of that module, or a consumer reaching the annotated declaration through its
      -- own imports would never see the entry.
      let anchor? :=
        if (env.getModuleIdxFor? decl).isNone then some decl
        else result.related?.filter fun r => (env.getModuleIdxFor? r).isNone
      let some anchor := anchor?
        | throwError "cannot record `@[{attrName}]` on `{decl}`: it is declared in an imported \
            module, so the annotation would sit in a module that a consumer reaching `{decl}` \
            does not import. Write the annotation in the module that declares `{decl}`."
      addEntry { attr := attrName, decl, payload := result.payload.compress } anchor
  }

end TrustAnnotations
