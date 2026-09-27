module

public import TrustAnnotations.Core

@[expose] public section

/-!
# `@[up_to]`: what a definition is determined up to

Some definitions pick one object among several that are equally good: a conditional expectation is
one function among those equal almost everywhere, a Radon–Nikodym derivative likewise, a generator
of a principal ideal is one up to a unit. Mathlib's definition returns a particular one, and nothing
in the term says that only the class is meant. That is intent, so it is the author's to declare:

```lean
@[up_to (· =ᵐ[μ] ·) "one version among those equal almost everywhere"]
noncomputable def condExp … (μ : Measure α) (f : α → E) : α → E := …
```

The relation is on the definition's result type, with the definition's arguments in scope under
their own names. A statement that tells apart two related values is then about the representative
the definition happens to pick, not about what it means: evaluating a conditional expectation at a
point, say. Finding such uses is an analyzer's job; this attribute records the declaration, and
checks that the relation is one on the right type.

What proves that the definition is determined up to the relation is a characterization whose
uniqueness theorem ends in it (`@[characterization]`): tools compare the two, and a declaration no
characterization backs is a claim.

A catalogue declares it for a definition of another library, like `@[domain]`:
`attribute [up_to (· =ᵐ[ν] ·)] MeasureTheory.Measure.rnDeriv`.

## Storage

As for `@[domain]`: the relation is also stored as a hidden declaration over the definition's
arguments, `condExp._upTo`, so that a tool can use it, and the entry (`up_to` in the generic
extension) records the relation applied to two variables and pretty-printed (`x =ᵐ[μ] y`), its head
constant (`Filter.EventuallyEq`), the note, and whether the author declared it in the definition's
own module (`"author"`) or a catalogue did (`"catalogue"`).

Not covered: a type determined up to isomorphism (an algebraic closure), since an isomorphism of
fields is not a relation on bare types. Mathlib's characteristic predicates (`IsAlgClosure`) are the
way to state that.
-/

open Lean Elab Meta

namespace TrustAnnotations

/-- One declaration of what a definition is determined up to: rebuilt from the generic extension by
`upToEntries`, not itself persisted. -/
structure UpToEntry where
  /-- The definition. -/
  decl : Name
  /-- The hidden declaration holding the relation, over the definition's arguments. -/
  relation : Name
  /-- The relation applied to two variables, pretty-printed (`x =ᵐ[μ] y`). -/
  statement : String
  /-- The relation's head constant (`Filter.EventuallyEq`), for comparing with characterizations. -/
  relationHead : Name := .anonymous
  /-- The note written with the declaration. Empty when omitted. -/
  note : String := ""
  /-- `"author"` when declared in the definition's own module, `"catalogue"` otherwise. -/
  source : String := "author"
deriving Repr, Inhabited, BEq

/-- The generic-extension entry recording an `@[up_to]` declaration. -/
def UpToEntry.toEntry (e : UpToEntry) : Entry :=
  { attr := `up_to, decl := e.decl
    payload := (Json.mkObj [("relation", toJson e.relation.toString),
      ("statement", toJson e.statement), ("relationHead", toJson e.relationHead.toString),
      ("note", toJson e.note), ("source", toJson e.source)]).compress }

/-- Every `@[up_to]` declaration visible in `env`, in declaration order. The entry point for tools. -/
def upToEntries (env : Environment) : Array UpToEntry :=
  (entriesOf env `up_to).filterMap fun e => do
    let j ← e.json.toOption
    let str (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
    let head := str "relationHead"
    return { decl := e.decl, relation := (str "relation").toName, statement := str "statement"
             relationHead := if head.isEmpty || head == "[anonymous]" then .anonymous else head.toName
             note := str "note", source := str "source" }

/-- What `decl` is declared to be determined up to, if anything. -/
def upToOf? (env : Environment) (decl : Name) : Option UpToEntry :=
  (upToEntries env).find? (·.decl == decl)

/-- The name of the hidden declaration holding the relation `decl` is determined up to. -/
def upToRelationName (decl : Name) : Name := decl.str "_upTo"

/-- The relation `stx` states for `decl`: the hidden declaration's value and type, the relation
applied to two variables and pretty-printed, its head constant, and whether it is plain equality.

A definition returning a function (`condExp … : α → E`) has more binders in its type than it has
arguments, and `(· =ᵐ[μ] ·)` relates functions, not their values. So the relation is elaborated
against what the definition returns after each prefix of its binders, deepest first, and the first
prefix it elaborates against, staying within it, is the definition's arity for this purpose. -/
private def elabUpTo (decl : Name) (stx : Syntax) :
    TermElabM (Expr × Expr × String × Name × Bool) := do
  let info ← getConstInfo decl
  forallTelescope info.type fun xs _ => do
    let mut found : Option (Nat × Expr × Expr) := none
    for k in (List.range (xs.size + 1)).reverse do
      let args := xs.extract 0 k
      let T ← instantiateForall info.type args
      let s ← saveState
      let r? ← try
          Term.withoutErrToSorry do
            let r ← Term.elabTermEnsuringType stx (← mkArrow T (← mkArrow T (mkSort Level.zero)))
            Term.synthesizeSyntheticMVarsNoPostponing
            let r ← instantiateMVars r
            if r.hasMVar || r.hasAnyFVar (fun f => !args.any (·.fvarId! == f)) then return none
            return some r
        catch _ => pure none
      match r? with
      | some r => found := some (k, T, r); break
      | none => s.restore
    let some (k, T, r) := found
      | throwError "`{stx}` is not a relation on what `{decl}` returns: `{decl}` has type\
          {indentExpr info.type}\nand the relation is expected to relate two values of the type it \
          returns, after its arguments"
    let args := xs.extract 0 k
    -- Shown applied to two variables, named as in the author's `fun` when it names them and the
    -- names are free: `f_1 n = g n` would read worse than `x n = y n`.
    let lctx ← getLCtx
    let (n₁, n₂) := match r with
      | .lam a _ (.lam b _ _ _) _ =>
        if a.hasMacroScopes || b.hasMacroScopes || lctx.usesUserName a || lctx.usesUserName b then
          (`x, `y)
        else (a, b)
      | _ => (`x, `y)
    let n₁ := (← getLCtx).getUnusedName n₁
    let (text, head, isEq) ← withLocalDeclD n₁ T fun a => do
      let n₂ := (← getLCtx).getUnusedName n₂
      withLocalDeclD n₂ T fun b => do
        let app := (mkApp2 r a b).headBeta
        -- equality of the two values themselves, not a relation that happens to be an equation
        let isEq := app.isAppOfArity ``Eq 3 && app.appFn!.appArg! == a && app.appArg! == b
        return ((← ppExpr app).pretty (width := 1000), app.getAppFn.constName?.getD .anonymous, isEq)
    return (← mkLambdaFVars args r,
      ← mkForallFVars args (← mkArrow T (← mkArrow T (mkSort Level.zero))), text, head, isEq)

/-- Records `stx` as the relation `decl` is determined up to: adds the hidden declaration to the
current module, and the entry anchored to it. -/
private def declareUpTo (decl : Name) (stx : Syntax) (note : String) : CoreM Unit := do
  let env ← getEnv
  let some info := env.find? decl
    | throwError "unknown declaration `{decl}`"
  if ← MetaM.run' (Meta.isProp info.type) then
    throwError "`up_to` belongs on a definition, but `{decl}` is a proof"
  if let some e := upToOf? env decl then
    throwError "`{decl}` is already declared to be determined up to `{e.statement}`"
  let rel := upToRelationName decl
  if env.contains rel then
    throwError "cannot declare what `{decl}` is determined up to: `{rel}` already exists"
  let source := if (env.getModuleIdxFor? decl).isNone then "author" else "catalogue"
  let (value, type, statement, relationHead, isEq) ← (elabUpTo decl stx).run'.run'
  if isEq then
    logWarning m!"`{decl}` is declared to be determined up to equality, which every definition is: \
      the declaration says nothing"
  addDecl (forceExpose := true) <| .defnDecl
    { name := rel, levelParams := info.levelParams, type, value
      hints := .abbrev, safety := .safe }
  addEntry ({ decl, relation := rel, statement, relationHead, note, source } : UpToEntry).toEntry rel

/-! ## The attribute -/

/--
`@[up_to R "note"]` declares that a definition is meant only up to the relation `R` on its result
type: any `R`-related value would do as well, and the one the definition returns is a
representative. The definition's arguments are in scope in `R` under their own names:
`@[up_to (· =ᵐ[μ] ·)]`. The note is optional.

On a definition of another library, for a catalogue: `attribute [up_to (· =ᵐ[ν] ·)] Measure.rnDeriv`.
-/
syntax (name := up_to) (priority := high) &"up_to" ppSpace term:max (ppSpace str)? : attr

initialize registerBuiltinAttribute {
  name := `up_to
  descr := "declare what a definition is determined up to"
  applicationTime := .afterTypeChecking
  add := fun decl stx attrKind => do
    unless attrKind == .global do
      throwError "`up_to` must be a global attribute: it is a claim about the definition, not about \
        a section or a namespace"
    let (termStx, noteStx?) ←
      if stx.getKind == ``Lean.Parser.Attr.simple then
        match stx[1].getOptional? with
        | some t => pure (t, none)
        | none => throwError "`@[up_to]` needs the relation, as `@[up_to (· =ᵐ[μ] ·)]`"
      else pure (stx[1], stx[2].getOptional?)
    let note := (noteStx?.bind Syntax.isStrLit?).getD ""
    declareUpTo decl termStx note
}

end TrustAnnotations
