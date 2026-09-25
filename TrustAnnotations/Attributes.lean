module

public import TrustAnnotations.Core

@[expose] public section

/-!
# The first attributes built on the generic extension

* `@[claim]` and `@[claim "reference"]`: this theorem is one of the results the project puts
  forward as its point, optionally with where it is stated informally (a paper and theorem number,
  a book section, a Wikidata item).
* `@[example_of d]`: this theorem states that some concrete object satisfies the definition `d`
  (a positive example). Evidence that `d` is not vacuous.
* `@[nonexample_of d]`: this theorem states that some concrete object does *not* satisfy `d` (a
  negative example). Evidence that `d` is not trivially true.

Each is recorded in the generic extension of `TrustAnnotations.Core`, so a tool reading annotations
needs to link that module only.

The attribute names are distinct from those of the `Characterization` package (`@[specifies]`,
`@[characterization]`): attribute names are global, and two packages claiming one name cannot be
imported together.
-/

open Lean

-- `priority := high` so that the argument-less `@[claim]` is not ambiguous with `Attr.simple`, the
-- catch-all attribute parser, which also matches it. The handler still accepts an `Attr.simple`
-- node, so the bare form keeps working whichever parser wins.
syntax (name := claim) (priority := high) &"claim" (ppSpace str)? : attr
syntax (name := example_of) &"example_of" ppSpace ident : attr
syntax (name := nonexample_of) &"nonexample_of" ppSpace ident : attr

namespace TrustAnnotations

/-- Checks that `decl` is a proposition, since the three attributes of this module annotate
statements. -/
def requireProof (attrName : Name) (decl : Name) : AttrM ConstantInfo := do
  let some info := (← getEnv).find? decl
    | throwError "unknown declaration `{decl}`"
  unless ← isProof info do
    throwError "`{attrName}` belongs on a theorem, but `{decl}` is not a proposition"
  return info

/-- Resolves and checks the definition an `example_of`/`nonexample_of` annotation is about. -/
def exampleTarget (attrName : Name) (decl : Name) (info : ConstantInfo) (id : Syntax) :
    AttrM Name := do
  let target ← Elab.realizeGlobalConstNoOverloadWithInfo id
  if target == decl then
    throwError "`{decl}` cannot be an example of itself"
  let some targetInfo := (← getEnv).find? target
    | throwError "unknown declaration `{target}`"
  if ← isProof targetInfo then
    throwError "`{target}` is a proof, but `{attrName}` names the definition that `{decl}` is \
      an example of"
  unless info.type.getUsedConstants.contains target do
    logWarning m!"`{decl}` is marked `@[{attrName} {target}]`, but its statement does not \
      mention `{target}`"
  return target

initialize
  registerAnnotationAttribute `claim
    "mark this theorem as one of the results the project puts forward" fun decl stx => do
      discard <| requireProof `claim decl
      let reference? ←
        if stx.getKind == ``Lean.Parser.Attr.simple then pure none
        else match stx with
          | `(attr| claim $[$ref?]?) => pure (ref?.map (·.getString))
          | _ => throwError "invalid `claim` attribute, expected `@[claim]` or `@[claim \"reference\"]`"
      let payload := match reference? with
        | some r => Json.mkObj [("reference", r)]
        | none => Json.mkObj []
      return { payload }

initialize
  registerAnnotationAttribute `example_of
    "mark this theorem as a positive example of a definition" fun decl stx => do
      let info ← requireProof `example_of decl
      let id ← match stx with
        | `(attr| example_of $id:ident) => pure id
        | _ => throwError "invalid `example_of` attribute, expected `@[example_of definition]`"
      let target ← exampleTarget `example_of decl info id
      return { payload := Json.mkObj [("target", toString target)], related? := some target }

initialize
  registerAnnotationAttribute `nonexample_of
    "mark this theorem as a negative example of a definition" fun decl stx => do
      let info ← requireProof `nonexample_of decl
      let id ← match stx with
        | `(attr| nonexample_of $id:ident) => pure id
        | _ => throwError "invalid `nonexample_of` attribute, expected `@[nonexample_of definition]`"
      let target ← exampleTarget `nonexample_of decl info id
      return { payload := Json.mkObj [("target", toString target)], related? := some target }

end TrustAnnotations
