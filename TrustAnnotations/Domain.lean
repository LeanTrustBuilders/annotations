module

public import TrustAnnotations.Core

@[expose] public section

/-!
# `@[domain]`: where a definition is meant to apply

Lean's functions are total. Outside the inputs a definition is meant for, it still returns
something — `x / 0 = 0`, `Real.log 0 = 0`, `∫ f = 0` for a non-integrable `f` — and nothing in the
term says which inputs those are. That is intent, so it is the author's to declare:

```lean
@[domain (0 ≤ p ∧ 0 < q) "0 · log (0 / q) = 0, by convention"]
noncomputable def klTerm (p q : ℝ) : ℝ := p * Real.log (p / q)
```

The domain is a proposition about the definition's arguments, which are in scope under the names
the definition gives them. A definition whose arguments have no names (one defined by pattern
matching) takes a function instead, `@[domain (fun n => 0 < n)]`, applied to its explicit arguments
and shown as written.
Either way the term goes in parentheses: the attribute reads a single argument, and without them
`q "…"` would be read as `q` applied to a string.

Declaring a domain is what lets a tool *check* a definition rather than guess at it: under its
declared domain, every operation in its body should be inside that operation's own domain, or its
value should not matter; and every use of the definition should stay inside the domain. Those checks
belong to an analyzer; this attribute only records the declaration, and checks its shape.

## Definitions you do not own

A catalogue of domains for another library's definitions applies the same attribute to them, in a
module of its own that the tools import:

```lean
attribute [domain (0 < x)] Real.log
```

The other attributes of this package refuse an imported declaration, because their entry would sit
in a module that a reader of that declaration never imports. Here that is the point — the catalogue
is read by importing it — and the entry is anchored to the hidden predicate below, which the
catalogue's own module declares.

## Storage

A tool needs the elaborated proposition, not only its text, and the generic extension holds names
and a string. So the domain is also stored as a hidden predicate over the definition's arguments,
`klTerm._domain`. Its name is internal (a component starting with `_`), so documentation, search and
completion skip it, as they skip equation lemmas; nobody writes, reads or uses it. Its body is
exported even under the module system, since the tools reading it are in other modules.

The entry, `domain` in the generic extension, records the definition, that predicate, the domain as
written (pretty-printed in the definition's own variable names), the note, and whether the author
declared it in the definition's own module (`"author"`) or a catalogue did (`"catalogue"`).
-/

open Lean Elab Meta

namespace TrustAnnotations

/-- One domain declaration: rebuilt from the generic extension by `domainEntries`, not itself
persisted. -/
structure DomainEntry where
  /-- The definition the domain is about. -/
  decl : Name
  /-- The hidden predicate holding the domain, over the definition's arguments. -/
  predicate : Name
  /-- The domain as written, pretty-printed in the definition's own variable names. -/
  statement : String
  /-- The note written with the declaration. Empty when omitted. -/
  note : String := ""
  /-- `"author"` when declared in the definition's own module, `"catalogue"` otherwise. -/
  source : String := "author"
deriving Repr, Inhabited, BEq

/-- The generic-extension entry recording a domain. -/
def DomainEntry.toEntry (e : DomainEntry) : Entry :=
  { attr := `domain, decl := e.decl
    payload := (Json.mkObj [("predicate", toJson e.predicate.toString),
      ("statement", toJson e.statement), ("note", toJson e.note),
      ("source", toJson e.source)]).compress }

/-- Every domain declaration visible in `env`, in declaration order. The entry point for tools. -/
def domainEntries (env : Environment) : Array DomainEntry :=
  (entriesOf env `domain).filterMap fun e => do
    let j ← e.json.toOption
    let str (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
    return { decl := e.decl, predicate := (str "predicate").toName, statement := str "statement"
             note := str "note", source := str "source" }

/-- The domain declared for `decl`, if any. -/
def domainOf? (env : Environment) (decl : Name) : Option DomainEntry :=
  (domainEntries env).find? (·.decl == decl)

/-- The name of the hidden predicate holding `decl`'s domain. -/
def domainPredicateName (decl : Name) : Name := decl.str "_domain"

/-- The domain `stx` states for `decl`, elaborated under `decl`'s binders: the predicate (a lambda
over all of `decl`'s arguments, with their binder infos), its type, and the proposition
pretty-printed in `decl`'s own variable names. -/
private def elabDomain (decl : Name) (stx : Syntax) : TermElabM (Expr × Expr × String) := do
  let info ← getConstInfo decl
  forallTelescope info.type fun xs _ => do
    let explicit ← xs.filterM fun x => return (← x.fvarId!.getBinderInfo).isExplicit
    let prop := mkSort Level.zero
    -- For the `fun` form the text is the function as written, whose variable names are the
    -- author's; the definition's own arguments have none to show.
    let (body, shown) ← Term.withoutErrToSorry do
      if stx.getKind == ``Lean.Parser.Term.paren && stx[1].getKind == ``Lean.Parser.Term.fun ||
          stx.getKind == ``Lean.Parser.Term.fun then
        let f ← Term.elabTermEnsuringType stx (← mkForallFVars explicit prop)
        Term.synthesizeSyntheticMVarsNoPostponing
        let f ← instantiateMVars f
        pure ((mkAppN f explicit).headBeta, f)
      else
        let e ← Term.elabTermEnsuringType stx prop
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        pure (e, e)
    if body.hasMVar then
      throwError "the domain of `{decl}` is not fully determined: {indentExpr body}"
    let text := (← ppExpr shown).pretty (width := 1000)
    return (← mkLambdaFVars xs body, ← mkForallFVars xs prop, text)

/-- Records `stx` as the domain of `decl`: adds the hidden predicate to the current module, and the
entry anchored to it. -/
private def declareDomain (decl : Name) (stx : Syntax) (note : String) : CoreM Unit := do
  let env ← getEnv
  let some info := env.find? decl
    | throwError "unknown declaration `{decl}`"
  if ← MetaM.run' (Meta.isProp info.type) then
    throwError "`domain` belongs on a definition, but `{decl}` is a proof: a theorem's hypotheses \
      already say where it applies"
  if let some e := domainOf? env decl then
    throwError "`{decl}` already has a declared domain, `{e.statement}`"
  let pred := domainPredicateName decl
  if env.contains pred then
    throwError "cannot declare the domain of `{decl}`: `{pred}` already exists"
  let source := if (env.getModuleIdxFor? decl).isNone then "author" else "catalogue"
  let (value, type, statement) ← (elabDomain decl stx).run'.run'
  if value.getUsedConstants.contains decl then
    logWarning m!"the domain declared for `{decl}` mentions `{decl}` itself: a domain says which \
      arguments the definition is meant for, so it is normally about the arguments alone"
  addDecl (forceExpose := true) <| .defnDecl
    { name := pred, levelParams := info.levelParams, type, value
      hints := .abbrev, safety := .safe }
  addEntry ({ decl, predicate := pred, statement, note, source } : DomainEntry).toEntry pred

/-! ## The attribute -/

/--
`@[domain (proposition) "note"]` declares where a definition is meant to apply: the proposition is
about the definition's arguments, under their own names. The note is optional; it is the place to
say what the value is outside the domain, or why the domain is what it is.

On a definition of another library, for a catalogue: `attribute [domain (0 < x)] Real.log`.
-/
syntax (name := domain) (priority := high) &"domain" ppSpace term:max (ppSpace str)? : attr

initialize registerBuiltinAttribute {
  name := `domain
  descr := "declare where a definition is meant to apply"
  applicationTime := .afterTypeChecking
  add := fun decl stx attrKind => do
    unless attrKind == .global do
      throwError "`domain` must be a global attribute: a domain is a claim about the definition, \
        not about a section or a namespace"
    -- `@[domain h]` with an identifier is also what `Attr.simple` accepts; both shapes are read.
    let (termStx, noteStx?) ←
      if stx.getKind == ``Lean.Parser.Attr.simple then
        match stx[1].getOptional? with
        | some t => pure (t, none)
        | none => throwError "`@[domain]` needs the domain, as `@[domain (0 < x)]`"
      else pure (stx[1], stx[2].getOptional?)
    let note := (noteStx?.bind Syntax.isStrLit?).getD ""
    declareDomain decl termStx note
}

end TrustAnnotations
