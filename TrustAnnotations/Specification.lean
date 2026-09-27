module

public import TrustAnnotations.Core

@[expose] public section

/-!
# `@[specifies]` and `@[characterization]`: the theorems that say what a definition means

A formalization's definitions are the part a reader has to take on faith: a proof can be checked by
the kernel, but nothing checks that `myDefinition` says what its name suggests. What settles that
question is a handful of theorems — that the definition agrees with the textbook formula on the
base case, that it is monotone, that it reduces to the classical notion in the classical case.

Those theorems already exist in most projects; what is missing is any record of *which* ones they
are. Nothing in the environment distinguishes a characterizing property of a definition from a step
in the proof of something else. `@[specifies]` is that record, written by the author at the point of
the theorem:

```lean
def entropy (p : Distribution α) : ℝ := …

@[specifies entropy "agrees with the textbook formula on finite supports"]
theorem entropy_eq_sum (p : Distribution α) (h : p.support.Finite) :
    entropy p = -∑ x ∈ h.toFinset, p x * Real.log (p x) := …

@[specifies entropy]
theorem entropy_nonneg (p : Distribution α) : 0 ≤ entropy p := …
```

Read back out of the compiled environment (`specEntries`), this gives a tool the two things it
could not otherwise derive: for a definition, the properties its author claims pin it down, and —
just as usefully — which definitions have no such claim at all.

## Importing this module

A file using the module system has to import this one at compile time — `meta import
TrustAnnotations` — because applying an attribute is a compile-time act and a runtime-phase import
does not run the initializer that registers it. Without that, `@[specifies]` is reported as an
unknown attribute. A file not using the module system just writes `import TrustAnnotations`.

## Why an attribute and not a metadata file

Because it cannot silently go stale. The target is an identifier, so it resolves against the
ambient namespaces, a typo is a compile error, and renaming the definition breaks the build at the
annotation. A sidecar file listing declaration names drifts out of date invisibly, which is the
one thing an auditing tool must not do.

## Reading the annotations from another process

Both attributes record their entries in the generic extension of `TrustAnnotations.Core`, as
annotations `specifies` (payload `{"target", "comment"}`) and `characterization` (payload
`{"role", "property", "target", "relation", "relationHead", "comment"}`, plus `{"form",
"candidate", "conditions", "context", "variables", "complete"}` for a characterization stated by one theorem) on
the annotated declaration. A tool reading a compiled project therefore reads them as it reads every other
attribute of this package, by linking the core once, and `specEntries` and `charEntries` rebuild the
records below from there. The payload keys are the on-disk format; the structures are not.

These attributes were first written as the `Characterization` package (and before that as
`LeanSpec`, in `LeanMachineLearning/exposition`), with extensions of their own; they moved here so
that one extension serves every annotation. Since then `@[characterization]` has gained a form with
no keyword and no predicate: a characterization stated by one theorem.

## The attribute name

Attribute names are global and unqualified, and Lean rejects a duplicate registration outright: if
a project imports two libraries that both claim a name, neither can be imported. The obvious name
here, `spec`, is already Lean's own — `Std.Tactic.Do` registers `@[spec]` for the specifications
its `mvcgen` verification-condition generator consumes — so this library takes `specifies`, which
also reads better at the use site. The token is declared non-reserved (`&"specifies"`), so a
project can still use `specifies` as an ordinary identifier.
-/

open Lean

namespace TrustAnnotations

/-- One `@[specifies …]` annotation: the theorem it was written on, the definition that theorem is
claimed to specify, and the author's optional note on why it belongs in the specification.

Rebuilt from the generic extension by `specEntries`; not itself persisted. -/
structure SpecEntry where
  /-- The annotated theorem. -/
  theoremName : Name
  /-- The definition the theorem is part of the specification of. -/
  target : Name
  /-- The author's justification, as written in the attribute. Empty when omitted. -/
  comment : String := ""
deriving Repr, Inhabited, BEq

/-- The generic-extension entry recording a `@[specifies]` annotation. -/
def SpecEntry.toEntry (e : SpecEntry) : Entry :=
  { attr := `specifies, decl := e.theoremName
    payload := (Json.mkObj [("target", toJson e.target.toString),
      ("comment", toJson e.comment)]).compress }

/-- Every specification annotation visible in `env`, in declaration order (so a definition's
specification reads in the order its author wrote it, not alphabetically).

This is the entry point for tools. It is a plain array rather than a map because the interesting
groupings differ per consumer — by target, by theorem, by module — and building the one you want
from a single pass is cheaper than maintaining all of them here. -/
def specEntries (env : Environment) : Array SpecEntry :=
  (entriesOf env `specifies).filterMap fun e => do
    let j ← e.json.toOption
    let target ← (j.getObjValAs? String "target").toOption
    return { theoremName := e.decl, target := target.toName
             comment := (j.getObjValAs? String "comment").toOption.getD "" }

/-- The definitions `thm` is annotated as specifying. Linear in the number of annotations in the
project; group `specEntries` yourself if you need this for every declaration. -/
def specTargetsOf (env : Environment) (thm : Name) : Array SpecEntry :=
  (specEntries env).filter (·.theoremName == thm)

/-- The theorems annotated as specifying `target`. Linear in the number of annotations in the
project; group `specEntries` yourself if you need this for every declaration. -/
def specTheoremsFor (env : Environment) (target : Name) : Array SpecEntry :=
  (specEntries env).filter (·.target == target)

/-! ## The attribute -/

/--
`@[specifies definition "why"]` marks a theorem as part of the specification of `definition`: one of
the properties its author offers as evidence that the definition is the intended one.

Both arguments are optional:

* `@[specifies]` infers the target from the theorem's own name, taking the innermost enclosing
  namespace that is a definition — so `@[specifies] theorem entropy_nonneg` in `namespace entropy`,
  or `@[specifies] theorem entropy.nonneg`, both mean `@[specifies entropy]`.
* the comment is free text, shown next to the theorem wherever the specification is presented. It
  should say what the property *buys* the reader, which the statement alone does not.

Apply it more than once for a theorem that specifies more than one definition
(`@[specifies foo, specifies bar]`).
-/
-- `priority := high` so that the argument-less `@[specifies]` is not ambiguous with `Attr.simple`,
-- the catch-all `ident`-shaped attribute parser, which also matches it. Without the priority both
-- parsers match to the same position and the category parser emits a `choice` node, which
-- `elabAttr` reports as the (nonexistent) attribute `choice`. The `add` handler below still
-- accepts an `Attr.simple` node, so the bare form keeps working whichever parser wins.
syntax (name := specifies) (priority := high) &"specifies" (ppSpace ident)? (ppSpace str)? : attr

register_option specifies.checkTargetMentioned : Bool := {
  defValue := true
  descr := "warn when a theorem carrying `@[specifies f]` does not mention `f` in its statement"
}

-- `isProof` is the core's: whether a declaration proves a proposition, decided from its type rather
-- than from its kind. An attribute handler runs under the visibility scope of the declaration it is
-- applied to, and in that exported view a theorem of the current module does not arrive as a
-- `.thmInfo`, so the syntactic test would silently pass theorems through.

/-- The declaration an entry about the pair `(a, b)` is anchored to — a local one.

Both attributes here relate two declarations, and neither requires them to be declared in the same
module: `attribute [specifies myDefinition] someImportedTheorem` and
`attribute [characterization property myDefinition] SomeImportedPredicate` are the shapes that let
one predicate characterize definitions in several modules without being copied into each. An
attribute writes its entry into the module being *elaborated*, so either of those records the claim
in a module that a reader of the local side reaches.

`none` when both are imported, which is the one configuration to reject: the entry would sit in a
module that neither `a` nor `b` points back to, so a consumer that reaches either of them through
its own imports would never see it.

The result also feeds `asyncDecl`, which has to name a declaration of the current async context
when there is one — under `@[attr]` on a declaration that context is the declaration itself, and a
standalone `attribute` command has none. -/
private def anchor? (env : Environment) (a b : Name) : Option Name :=
  if (env.getModuleIdxFor? a).isNone then some a
  else if (env.getModuleIdxFor? b).isNone then some b
  else none

/-- The definition a bare `@[specifies]` refers to: the innermost enclosing namespace of `declName`
that names something a specification can be about. Walks outwards (`Foo.Bar.baz` tries `Foo.Bar`,
then `Foo`) so that a theorem in a nested namespace still finds its subject, skipping ancestors
that are themselves proofs, and gives up when no ancestor names a constant at all — in which case
the author has to be explicit. -/
private partial def inferTarget (declName : Name) : AttrM (Option Name) :=
  go declName.getPrefix
where
  go : Name → AttrM (Option Name)
    | .anonymous => return none
    | n => do
      match (← getEnv).find? n with
      | some info => if ← isProof info then go n.getPrefix else return some n
      | none => go n.getPrefix

initialize registerBuiltinAttribute {
  name := `specifies
  descr := "mark this theorem as part of the specification of a definition"
  applicationTime := .afterTypeChecking
  add := fun declName stx attrKind => do
    unless attrKind == .global do
      throwError "`specifies` must be a global attribute: a specification is a claim about the \
        definition, not about a section or a namespace"
    -- `Attr.simple` is the bare `@[specifies]` as parsed by the catch-all attribute parser; see the
    -- note on the syntax declaration above.
    let (targetStx?, commentStx?) ←
      if stx.getKind == ``Lean.Parser.Attr.simple then
        pure (none, none)
      else match stx with
        | `(attr| specifies $[$targetStx?]? $[$commentStx?]?) => pure (targetStx?, commentStx?)
        | _ => throwError "invalid `specifies` attribute, expected \
          `@[specifies definition \"comment\"]`"
    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration `{declName}`"

    -- `@[specifies]` says "this statement is part of what `f` means", so it only makes sense on
    -- something that has a statement. Anything proving a proposition qualifies, so that a `lemma`
    -- elaborated as a `def` (or an `instance` of a `Prop`-valued class) is still accepted.
    unless (← isProof info) do
      throwError "`specifies` belongs on a theorem, but `{declName}` is not a proposition"

    let target ← match targetStx? with
      | some id => Elab.realizeGlobalConstNoOverloadWithInfo id
      | none =>
        match ← inferTarget declName with
        | some target => pure target
        | none =>
          throwError "cannot infer what `{declName}` specifies: no enclosing namespace of its \
            name is a declaration. Name the definition explicitly, as `@[specifies myDefinition]`"
    if target == declName then
      throwError "`{declName}` cannot be part of its own specification"
    let some targetInfo := env.find? target
      | throwError "unknown declaration `{target}`"
    if ← isProof targetInfo then
      throwError "`{target}` is itself a proof, but `specifies` names the definition that the \
        annotated theorem is a property of"
    let some anchor := anchor? env declName target
      | throwError "cannot record that `{declName}` specifies `{target}`: both are declared in \
          imported modules, so the entry would sit in a module neither of them points back to and \
          a consumer reaching either through its own imports would not see it. Write the \
          annotation in the module that declares one of them."

    if (specEntries env).any fun e => e.theoremName == declName && e.target == target then
      throwError "`{declName}` is already part of the specification of `{target}`"

    -- A theorem that never mentions its target is almost always a mistyped or copy-pasted
    -- annotation. It is only *almost* always, though — the target can be reached through an
    -- abbreviation, or hidden in a structure projection that the elaborated type does not name as
    -- a constant — so this is a warning, and a theorem living inside the target's namespace is
    -- taken as intent enough to say nothing at all.
    if specifies.checkTargetMentioned.get (← getOptions) then
      unless info.type.getUsedConstants.contains target || target.isPrefixOf declName do
        logWarning m!"`{declName}` is marked as part of the specification of `{target}`, but its \
          statement does not mention `{target}`. Set `specifies.checkTargetMentioned` to `false` \
          to silence this."

    let comment := (commentStx?.map TSyntax.getString).getD ""
    addEntry ({ theoremName := declName, target, comment } : SpecEntry).toEntry anchor
}

/-!
## `@[characterization]` — the theorems that pin a definition down

`@[specifies]` records a claim, and nothing checks it beyond the target resolving. A
*characterization* is the stronger thing, and it is checkable. It comes in three parts:

* a **property** — a predicate `P` with an argument of the definition's type;
* an **existence** theorem — that the definition satisfies `P`;
* a **uniqueness** theorem — that anything satisfying `P` is related to anything else satisfying
  `P` by some relation `R`.

Together those say: the definition is *the* object with property `P`, up to `R`.

```lean
@[characterization property entropy "the Shannon axioms"]
def IsEntropy (p : Distribution α) (h : ℝ) : Prop := …

@[characterization existence]
theorem isEntropy_entropy (p : Distribution α) : IsEntropy p (entropy p) := …

@[characterization uniqueness]
theorem IsEntropy.unique (h₁ : IsEntropy p x) (h₂ : IsEntropy p y) : x = y := …
```

The two theorems name the *predicate*, not the definition, and by default read it off their own
statements. The predicate is the hub because a definition can have more than one characterization
— entropy by the Shannon axioms and entropy by a variational formula — and hanging every part off
the definition would let a tool assemble the pieces of one into the other.

`R` is a relation rather than equality outright because plenty of objects are only determined up
to a.e. equality, or up to isomorphism.

### What is checked, and what is not

The shapes are checked by `isDefEq`, not by matching syntax: the existence theorem's statement has
to *be* `P … (definition …)`, and the uniqueness theorem's has to relate two objects that its own
hypotheses say satisfy `P`. A tool reading a complete bundle back out can therefore report
"characterized" as a checked fact rather than as an author's assertion, which is the whole
difference from `@[specifies]`.

What is *not* checked is that the characterization says anything. `P x := (x = definition)` is a
well-formed characterization that conveys nothing, and so is a `P` that is subtly the wrong
property. The checks buy well-formedness; the reader still has to read `P` and `R`, which is why
any presentation of a characterization has to show both in full, and why a predicate mentioning
the definition it characterizes draws a warning (`characterization.checkNotCircular`).

Two further gaps, both deliberate:

* nothing requires `P` to be `R`-invariant, so a bundle gives `P x → R x definition` and not the
  converse. The first is what a reader needs; the second is extra work for no gain here.
* uniqueness is propositional. "Unique up to *unique* isomorphism" is a term-level statement, and
  a characterization recorded here with `R x y := Nonempty (x ≃ y)` loses the canonicity. For
  universal properties, Mathlib's bundled `IsColimit`-style formulation is the right tool and this
  is a weaker shadow of it.

### Feeding `specEntries`

Both theorems of a characterization are also, trivially, part of the specification of the
definition, so each writes a `SpecEntry` as well. A consumer that only knows about `@[specifies]`
— "which definitions has nobody said anything about" — keeps working without learning about the
second extension.

### One attribute name, and no attribute on the relation

Attribute names are global and unqualified, and a collision between two libraries makes them
mutually un-importable (see the note on the `specifies` name above). The three roles therefore
share one registered name, distinguished by a mandatory keyword.

The relation gets no attribute at all: it is read off the uniqueness theorem's conclusion. That is
the only thing that could work — a relation like `Setoid.r s` is a partial application with no
declaration to annotate in the first place, and requiring one on `Eq` and `Filter.EventuallyEq`
would make every project re-annotate core and Mathlib before it could state a uniqueness theorem.

### Where the annotation lives

A predicate and the definition it characterizes need not be declared in the same module, and the
case that needs them not to be is a *shared* predicate — `IsCondExp`, say — registered against
each of several definitions from those definitions' own modules:

```lean
attribute [characterization property myDefinition] SomeImportedPredicate
```

An attribute writes its entry into the module being elaborated, so this records the claim where a
reader of `myDefinition` finds it. Without it a shared predicate would have to be copied, once per
definition, into every module that wanted to use it.

What is rejected is only the case where the two declarations an entry relates are *both* imported.
The entry would then sit in a module neither of them points back to, and a consumer that reached
either through its own imports would never see it. Same rule for `@[specifies]`, whose entries
relate a theorem and a definition.

### Storage

Like `@[specifies]`, recorded in the generic extension, as the `characterization` payload the module
docstring describes: the payload keys are the format, and `CharEntry` is rebuilt from them.
-/

/-- Which of the three parts of a characterization a `@[characterization …]` annotation records.

Recorded by its keyword (`CharRole.keyword`). -/
inductive CharRole where
  /-- The predicate an object of the definition's type may or may not satisfy. -/
  | property
  /-- The theorem that the definition satisfies the predicate. -/
  | existence
  /-- The theorem that the predicate determines its subject up to a relation. -/
  | uniqueness
  /-- A characterization stated by one theorem, with no predicate: an iff, or a uniqueness theorem
  whose hypotheses are the property (`@[characterization]` with no keyword). -/
  | «theorem»
deriving Repr, Inhabited, BEq

/-- The keyword that selects this role in the attribute. -/
def CharRole.keyword : CharRole → String
  | .property => "property"
  | .existence => "existence"
  | .uniqueness => "uniqueness"
  | .theorem => "theorem"

/-- The role a keyword selects. -/
def CharRole.ofKeyword? : String → Option CharRole
  | "property" => some .property
  | "existence" => some .existence
  | "uniqueness" => some .uniqueness
  | "theorem" => some .theorem
  | _ => none

/-- One condition of a characterization stated by a theorem: a hypothesis on the candidate object
(or, for an iff, the property side), and whether the definition was shown to satisfy it. -/
structure CharCondition where
  /-- The condition, pretty-printed with the theorem's own variable names. -/
  text : String
  /-- Whether the definition, put in the candidate's place, was shown to satisfy it. -/
  proved : Bool
  /-- The theorems that showed it; empty when it followed from the context or by reflexivity. -/
  provedBy : Array Name := #[]
  /-- The premises of those theorems that were assumed rather than shown: conditions on the
  definition's arguments under which it satisfies this condition. -/
  assuming : Array String := #[]
deriving Repr, Inhabited, BEq

/-- One `@[characterization …]` annotation: the declaration it was written on, which part of a
characterization that declaration is, and the predicate/definition pair the part belongs to.

Both `property` and `target` are recorded on every entry, including the theorems, so that the
parts of one characterization can be grouped without re-deriving anything — a predicate may
characterize more than one definition, and a theorem belongs to exactly one of those bundles.

Rebuilt from the generic extension by `charEntries`; not itself persisted. -/
structure CharEntry where
  /-- The annotated declaration. -/
  declName : Name
  /-- What this declaration contributes. -/
  role : CharRole
  /-- The characterizing predicate. Equal to `declName` on a `.property` entry. -/
  property : Name
  /-- The definition being characterized. -/
  target : Name
  /-- On a `.uniqueness` entry, the theorem's conclusion as written, pretty-printed with its own
  variable names (`x = y`, `f =ᵐ[μ] g`) — the "up to what" of the characterization, and the thing
  a presentation should show. Empty on the other roles. -/
  relation : String := ""
  /-- On a `.uniqueness` entry, the head constant of that conclusion (`Eq`,
  `Filter.EventuallyEq`, …), for grouping and filtering. Anonymous when there is none, and on the
  other roles. -/
  relationHead : Name := .anonymous
  /-- The author's justification, as written in the attribute. Empty when omitted. -/
  comment : String := ""
  /-- On a `.theorem` entry: `"iff"` or `"uniqueness"`. Empty on the other roles. -/
  form : String := ""
  /-- On a `.theorem` entry: the name of the candidate object, the variable the relation relates to
  the definition. -/
  candidate : String := ""
  /-- On a `.theorem` entry: the property, one condition per hypothesis on the candidate (and the
  other side of an iff), each with whether the definition was shown to satisfy it. -/
  conditions : Array CharCondition := #[]
  /-- On a `.theorem` entry: every assumption of the theorem that is not about the candidate,
  as written — its other hypotheses (`m ≤ m₀`, `Integrable f μ`) and all its instance arguments,
  in brackets (`[CompleteSpace E]`, `[SigmaFinite (μ.trim hm)]`). Where the characterization
  holds. Nothing is left out: a missing assumption would make the characterization look more
  general than it is. -/
  context : Array String := #[]
  /-- On a `.theorem` entry: the theorem's other binders, the variables it is about
  (`μ : Measure α`), so that the whole context is recorded. -/
  variables : Array String := #[]
  /-- On a `.theorem` entry: the definition's arguments that the characterization fixes rather than
  quantifies over (`G := ℝ`), so that it covers only that case. Empty when it is as general as the
  definition. -/
  specialized : Array String := #[]
deriving Repr, Inhabited, BEq

/-- Whether a characterization stated by a theorem is complete: the definition was shown to satisfy
every condition, so that it is *the* object with the property. The other roles are completed by
assembling their parts (`Characterization.isComplete`). -/
def CharEntry.complete (e : CharEntry) : Bool :=
  e.role == .theorem && e.conditions.all (·.proved)

/-- The generic-extension entry recording a `@[characterization]` annotation. -/
def CharEntry.toEntry (e : CharEntry) : Entry :=
  let base := [("role", toJson e.role.keyword),
      ("property", toJson e.property.toString), ("target", toJson e.target.toString),
      ("relation", toJson e.relation), ("relationHead", toJson e.relationHead.toString),
      ("comment", toJson e.comment)]
  let extra := if e.role != .theorem then [] else
    [("form", toJson e.form), ("candidate", toJson e.candidate),
     ("conditions", Json.arr (e.conditions.map fun c => Json.mkObj [("text", toJson c.text),
        ("proved", toJson c.proved), ("by", toJson (c.provedBy.map (·.toString))),
        ("assuming", toJson c.assuming)])),
     ("context", toJson e.context), ("variables", toJson e.variables),
     ("specialized", toJson e.specialized), ("complete", toJson e.complete)]
  { attr := `characterization, decl := e.declName, payload := (Json.mkObj (base ++ extra)).compress }

/-- Every characterization annotation visible in `env`, in declaration order. The entry point for
tools that want the parts; most will want `characterizations` instead, which assembles them. -/
def charEntries (env : Environment) : Array CharEntry :=
  (entriesOf env `characterization).filterMap fun e => do
    let j ← e.json.toOption
    let str (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
    let role ← CharRole.ofKeyword? (str "role")
    let relationHead := str "relationHead"
    let conditions := ((j.getObjValAs? (Array Json) "conditions").toOption.getD #[]).filterMap
      fun c => do
        let text ← (c.getObjValAs? String "text").toOption
        let proved := (c.getObjValAs? Bool "proved").toOption.getD false
        let provedBy := ((c.getObjValAs? (Array String) "by").toOption.getD #[]).map (·.toName)
        let assuming := (c.getObjValAs? (Array String) "assuming").toOption.getD #[]
        return ({ text, proved, provedBy, assuming } : CharCondition)
    return { declName := e.decl, role, property := (str "property").toName
             target := (str "target").toName, relation := str "relation"
             relationHead := if relationHead.isEmpty || relationHead == "[anonymous]" then .anonymous
               else relationHead.toName
             comment := str "comment", form := str "form", candidate := str "candidate"
             conditions, context := (j.getObjValAs? (Array String) "context").toOption.getD #[]
             variables := (j.getObjValAs? (Array String) "variables").toOption.getD #[]
             specialized := (j.getObjValAs? (Array String) "specialized").toOption.getD #[] }

/-- The definitions `pred` is registered as characterizing. Empty for a predicate that carries no
`@[characterization property]`, which is what the attribute uses to reject a theorem pointing at
something nobody declared to be a characterizing property. -/
def characterizedBy (env : Environment) (pred : Name) : Array Name :=
  (charEntries env).filterMap fun e =>
    if e.role == .property && e.property == pred then some e.target else none

/-- One definition, one property claimed to characterize it, and the theorems supplying the two
halves of that claim.

Assembled from `charEntries`; not itself persisted, so its layout is free to change. -/
structure Characterization where
  /-- The characterizing predicate. -/
  property : Name
  /-- The definition it characterizes. -/
  target : Name
  /-- The author's note on the predicate. -/
  comment : String := ""
  /-- The theorems stating that `target` satisfies `property`. -/
  existence : Array CharEntry := #[]
  /-- The theorems stating that `property` determines its subject up to a relation. -/
  uniqueness : Array CharEntry := #[]
deriving Repr, Inhabited

/-- Whether both halves of the claim are present. A characterization with a property and an
existence theorem but no uniqueness theorem says no more than a `@[specifies]` annotation does:
the definition has the property, and so might anything else. -/
def Characterization.isComplete (c : Characterization) : Bool :=
  !c.existence.isEmpty && !c.uniqueness.isEmpty

/-- Every characterization visible in `env`, complete or not, in declaration order of the
predicates.

Quadratic in the number of annotations, like `specTheoremsFor`; group `charEntries` yourself if
you need this for a whole library at once. -/
def characterizations (env : Environment) : Array Characterization :=
  let entries := charEntries env
  entries.filterMap fun p =>
    -- A characterization stated by one theorem is its own bundle: the theorem is the uniqueness
    -- half, and the existence half too once the definition was shown to satisfy every condition.
    if p.role == .theorem then
      some { property := p.declName, target := p.target, comment := p.comment
             existence := if p.complete then #[p] else #[], uniqueness := #[p] }
    else if p.role != .property then none
    else some {
      property := p.property
      target := p.target
      comment := p.comment
      existence := entries.filter fun e =>
        e.role == .existence && e.property == p.property && e.target == p.target
      uniqueness := entries.filter fun e =>
        e.role == .uniqueness && e.property == p.property && e.target == p.target }

/-- The characterizations claimed for `target`, complete or not. -/
def characterizationsOf (env : Environment) (target : Name) : Array Characterization :=
  (characterizations env).filter (·.target == target)

/-- Whether some property is claimed to characterize `target` *and* both halves of that claim have
been supplied. This is the question the audit asks: a definition that is merely specified is one a
reader has to take partly on faith, and one that is characterized is not. -/
def isCharacterized (env : Environment) (target : Name) : Bool :=
  (characterizationsOf env target).any (·.isComplete)

/-! ### Reading the shapes

Everything below decides, from elaborated types, whether a declaration really has the shape its
annotation claims. Three rules hold throughout:

* comparison is `isDefEq`, not syntactic matching, so a theorem stated in unfolded form still
  counts. The price is that the predicate has to be a `def`, `structure` or `class` the elaborator
  can see through, not something `opaque`.
* metavariables are created *inside* whatever telescope they will be unified against. A
  metavariable cannot be assigned a free variable introduced after it was created, so opening the
  predicate before entering the theorem's binders would make every check fail.
* a trial that may fail runs under `withoutModifyingState`, since a failed `isDefEq` can leave
  partial assignments behind that would poison the next trial.
-/

/-- `pred` applied to fresh metavariables, paired with the metavariable in its last argument
position — the *characterized slot*, the one an object of the definition's type goes into.

`none` when `pred` is not a predicate at all: it has to take at least one argument and land in
`Prop`. The last argument is the slot by convention; a predicate with several arguments of the
definition's type characterizes the last of them. -/
private def openPredicate (pred : Name) : MetaM (Option (Expr × Expr)) := do
  let P ← Meta.mkConstWithFreshMVarLevels pred
  let (args, _, body) ← Meta.forallMetaTelescope (← Meta.inferType P)
  if args.isEmpty then return none
  unless (← instantiateMVars body).isProp do return none
  return some (mkAppN P args, args.back!)

/-- `target` applied to fresh metavariables, at every arity from fully applied down to bare.

A characterization can be of the definition applied to its arguments (`IsCondExp μ f (μ[f|m])`,
the usual case) or of the definition itself as a function, and nothing in the annotation says
which, so both are tried — fully applied first, since that is what authors mean far more often. -/
private def openTargetAtEachArity (target : Name) : MetaM (Array Expr) := do
  let d ← Meta.mkConstWithFreshMVarLevels target
  let (args, _, _) ← Meta.forallMetaTelescope (← Meta.inferType d)
  return (Array.range (args.size + 1)).reverse.map fun k => mkAppN d (args.extract 0 k)

/-- Whether `pred` is a predicate on the type of `target`: its characterized slot accepts `target`
applied to some prefix of `target`'s own arguments. -/
private def isPredicateOn (pred target : Name) : MetaM Bool := do
  let some (_, slot) ← openPredicate pred | return false
  let slotType ← Meta.inferType slot
  for t in ← openTargetAtEachArity target do
    let tType ← Meta.inferType t
    if ← withoutModifyingState (Meta.isDefEq slotType tType) then return true
  return false

/-- Whether `thmType` states that `target` satisfies `pred` — that is, whether it is, under its
binders, `pred` applied to arguments whose last is `target` applied to some prefix of its own.

Forcing the slot to be `target` *before* unifying the whole statement is what makes a single
error message possible: without it a statement of the right shape about the wrong object would
leave the slot holding something else, or nothing at all.

The one false negative worth knowing about: the witness has to be *built from* the definition,
syntactically. `IsDouble 2 4` says that `double 2` satisfies `IsDouble 2`, and says it
definitionally, but unification cannot run `double` backwards to discover that, so it is rejected.
Writing the witness as `double 2` is both accepted and clearer. -/
private def statesExistence (thmType : Expr) (pred target : Name) : MetaM Bool :=
  Meta.forallTelescopeReducing thmType fun _ concl => do
    let some (papp, slot) ← openPredicate pred | return false
    for t in ← openTargetAtEachArity target do
      let ok ← withoutModifyingState do
        if ← Meta.isDefEq slot t then Meta.isDefEq concl papp else return false
      if ok then return true
    return false

/-- If `e` is `pred` applied to arguments, the object in its characterized slot.

`none` also when the slot comes back undetermined: a hypothesis that does not say *which* object
satisfies the property is not one the conclusion can be relating. -/
private def predSlotIn? (pred : Name) (e : Expr) : MetaM (Option Expr) :=
  withoutModifyingState do
    let some (papp, slot) ← openPredicate pred | return none
    unless ← Meta.isDefEq e papp do return none
    let s ← instantiateMVars slot
    -- `s` is built from the ambient free variables, so it outlives the state restore; a leftover
    -- metavariable would not.
    return if s.hasExprMVar then none else some s

/-- Whether `thmType` states that `pred` determines its subject up to a relation, and if so that
relation: the conclusion as written, and its head constant.

Two shapes are accepted, both after telescoping the binders:

* `… → pred … x → … → pred … y → R x y`, two hypotheses in `pred`, related to each other;
* `… → pred … x → … → R x (target …)`, one hypothesis, related to the definition itself. That is
  the form Mathlib usually writes (`condExp_unique`) and it is just as good: with the existence
  theorem in hand, `P x → R x definition` is exactly the conclusion a reader wants, and no
  symmetry of `R` is needed to get there.

The relation has to be *applied* — the conclusion's last two arguments are the related pair. One
written inline, as `Nonempty (x ≃ y)` is, has to be given a name and stated as `IsoRel x y`, which
a presentation wants anyway for the same reason it wants a named predicate: something to show the
reader and link to. -/
private def statesUniqueness (thmType : Expr) (pred target : Name) :
    MetaM (Option (String × Name)) :=
  Meta.forallTelescopeReducing thmType fun binders concl => do
    let args := concl.getAppArgs
    if args.size < 2 then return none
    let lhs := args[args.size - 2]!
    let rhs := args[args.size - 1]!
    let sameTerm (x y : Expr) : MetaM Bool := withoutModifyingState (Meta.isDefEq x y)
    -- whether the conclusion relates `a` and `b`, in either order
    let relates (a b : Expr) : MetaM Bool := do
      if (← sameTerm lhs a) && (← sameTerm rhs b) then return true
      if (← sameTerm lhs b) && (← sameTerm rhs a) then return true
      return false
    let mut slots := #[]
    for b in binders do
      if let some s ← predSlotIn? pred (← Meta.inferType b) then
        slots := slots.push s
    let mut ok := false
    for a in slots do
      for b in slots do
        unless a == b do
          if ← relates a b then ok := true
    unless ok do
      let targets ← openTargetAtEachArity target
      for a in slots do
        for t in targets do
          if ← relates a t then ok := true
    unless ok do return none
    return some ((← Meta.ppExpr concl).pretty (width := 1000),
      concl.getAppFn.constName?.getD .anonymous)

/-- The characterizing property `declName` is about, guessed from its own statement: for an
existence theorem the head of the conclusion, for a uniqueness theorem the head of the first
hypothesis that names one. Only constants already registered as characterizing properties count,
which is what keeps the guess from latching onto an unrelated `Membership` or `Filter`.

Deliberately syntactic where the shape checks are not: this decides *which* claim is being made,
and a near-miss here would silently file the annotation under the wrong predicate rather than
report that the author has to be explicit. -/
private def inferProperty (env : Environment) (thmType : Expr) (role : CharRole) :
    MetaM (Option Name) :=
  Meta.forallTelescopeReducing thmType fun binders concl => do
    let registered (n : Name) : Bool := !(characterizedBy env n).isEmpty
    if role == .existence then
      match concl.getAppFn.constName? with
      | some n => return if registered n then some n else none
      | none => return none
    for b in binders do
      if let some n := (← Meta.inferType b).getAppFn.constName? then
        if registered n then return some n
    return none

/-- The constants a candidate property is built out of. A `structure` or `class` has its fields'
types nowhere in here, so the circularity check below does not see through one — a limitation, not
a soundness hole, since the check is a warning either way. -/
private def predicateUses (info : ConstantInfo) : Array Name :=
  info.type.getUsedConstants ++ (info.value?.map Expr.getUsedConstants).getD #[]

/-- `` `a` ``, `` `a` and `b` ``, `` `a`, `b` and `c` `` — for listing candidate targets in an
error message. -/
private def andList (ns : Array Name) : MessageData :=
  match ns.toList.reverse with
  | [] => m!"nothing"
  | [n] => m!"`{n}`"
  | n :: rest =>
    m!"{MessageData.joinSep (rest.reverse.map fun r => m!"`{r}`") ", "} and `{n}`"

/-! ### A characterization stated by one theorem

`@[characterization]` with no keyword needs no predicate. The theorem is the characterization:

* an **iff**, `R x (d …) ↔ Q x`: `Q` is the property, and the theorem says both halves at once;
* a **uniqueness theorem**, `H₁ x → … → Hₙ x → R x (d …)`: its hypotheses on `x` are the property.

`x` is the *candidate*, a variable the theorem quantifies over; `d` is the definition, read off the
other side of the relation (or named, as `@[characterization d]`); `R` is the relation, read off the
conclusion as for a uniqueness theorem of the other form.

The property is only half of it: `d` has to satisfy it. For an iff that is `R (d …) (d …)`, so
reflexivity. For a uniqueness theorem, each hypothesis `Hᵢ (d …)` is proved from the `@[specifies d]`
theorems declared so far, applied a few deep, with the theorem's other hypotheses in context — so
existence costs no new declaration either: the specification theorems a definition has anyway are
what show it. A condition nothing shows is recorded as such, and the characterization as incomplete.

Existence often needs more than uniqueness does: `⟨M⟩` compensates `M²` only for a square-integrable
adapted `M`, while any two compensators agree without that. So a premise of a specification theorem
that the context does not provide may be *assumed*, and is recorded as a condition under which `d`
has the property (`CharCondition.assuming`). The uniqueness theorem then needs no hypothesis its own
proof does not use. Only a premise can be assumed, never the condition itself, and only a
proposition about the theorem's own variables that does not mention `d`: a condition on `d`'s
arguments, not on its value.
-/

section TheoremForm
open Meta

/-- Proves `goal` from `lemmas` and the local context: by an assumption, or after introductions by
an assumption, by reflexivity, by an instance, or by one of `lemmas` whose premises are proved the
same way, `fuel` applications deep. The lemmas used and the premises assumed, or `none`.

The assumption comes first because a premise is often a hypothesis of the theorem as it stands,
`∀ n, Measurable (A n)` say: introducing its binders first would leave a goal that no hypothesis
matches.

A premise of an applied lemma (`premise`) that nothing proves may be *assumed* when `assumable` says
so: it is then recorded as a condition under which the definition has the property. The goal itself
never is. Among the lemmas that apply, one needing no assumption is taken at once, and otherwise
the one needing fewest. -/
private partial def proveFrom (lemmas : Array Name) (assumable : Expr → MetaM Bool) (fuel : Nat)
    (goal : MVarId) (premise : Bool := false) : MetaM (Option (Array Name × Array Expr)) := do
  let original ← instantiateMVars (← goal.getType)
  if (← observing? goal.assumption).isSome then return some (#[], #[])
  let (_, goal) ← goal.intros
  if (← observing? goal.assumption).isSome then return some (#[], #[])
  if (← observing? goal.applyRfl).isSome then return some (#[], #[])
  let type ← goal.getType
  if (← isClass? type).isSome then
    if let some inst ← observing? (synthInstance type) then
      goal.assign inst
      return some (#[], #[])
  let mut best : Option (Array Name × Array Expr) := none
  if fuel > 0 then
    for l in lemmas do
      -- Each trial in a state of its own: only whether it succeeds, and what it assumes, is kept.
      let r ← withoutModifyingState <| observing? do
        let subgoals ← goal.apply (← mkConstWithFreshMVarLevels l) { allowSynthFailures := true }
        let mut used := #[l]
        let mut assumed := #[]
        for g in subgoals do
          if ← g.isAssigned then continue
          let some (u, a) ← proveFrom lemmas assumable (fuel - 1) g (premise := true)
            | throwError "a premise is not proved"
          used := used ++ u
          assumed := assumed ++ a
        return (used, assumed)
      if let some (u, a) := r then
        if a.isEmpty then return some (u, a)
        if best.all (a.size < ·.2.size) then best := some (u, a)
  if best.isSome then return best
  if premise && (← assumable original) then return some (#[], #[original])
  return none

/-- What a characterization stated by one theorem says, read off its statement. -/
private structure TheoremShape where
  form : String
  target : Name
  candidate : String
  relation : String
  relationHead : Name
  conditions : Array CharCondition
  context : Array String
  variables : Array String
  specialized : Array String
  /-- Whether the property mentions the definition it characterizes. -/
  circular : Bool

/-- The definition `defn` is `target` applied to arguments, when `explicit?` names it; otherwise the
head constant of `defn`, when that is a definition. -/
private def definitionIn? (defn : Expr) (explicit? : Option Name) : MetaM (Option Name) := do
  match explicit? with
  | some t =>
    for d in ← openTargetAtEachArity t do
      if ← withoutModifyingState (isDefEq defn d) then return some t
    return none
  | none =>
    let some h := defn.getAppFn.constName? | return none
    let some info := (← getEnv).find? h | return none
    if ← Meta.isProp info.type then return none
    return some h

/-- Reads `thmType` as a characterization stated by one theorem, trying the relation's two sides as
the candidate, and for an iff its two sides as the relation. Existence is proved from `lemmasFor`
the definition found. `none` when no reading fits. -/
private def readTheorem (thmType : Expr) (levelParams : List Name) (explicit? : Option Name)
    (lemmasFor : Name → Array Name) : MetaM (Option TheoremShape) :=
  forallTelescopeReducing thmType fun xs concl => do
    let readings : Array (Expr × Option Expr) := match concl.iff? with
      | some (a, b) => #[(a, some b), (b, some a)]
      | none => #[(concl, none)]
    for (rel, other?) in readings do
      -- The candidate and the definition are the relation's last two arguments (`g =ᵐ[μ] condExp …`),
      -- or, for a type determined up to isomorphism, the first two explicit arguments of the
      -- isomorphism type (`Nonempty (K ≃+*o ℝ)`), whose last arguments are instances. An isomorphism
      -- that also preserves more (`∃ e : K ≃+*o ℝ, e 0 = 0 ∧ …`) pins down every operation the
      -- statement names: `ℝ`'s `0` is its own definition, not the ring structure's.
      let inner := if rel.isAppOfArity ``Nonempty 1 then rel.appArg!
        else if rel.isAppOfArity ``Exists 2 then rel.appFn!.appArg!
        else rel
      let mut pairs : Array (Expr × Expr) := #[]
      let args := rel.getAppArgs
      if args.size ≥ 2 then pairs := pairs.push (args[args.size - 2]!, args[args.size - 1]!)
      if inner.getAppFn.isConst then
        let info ← getFunInfoNArgs inner.getAppFn inner.getAppNumArgs
        let explicitArgs := (inner.getAppArgs.zip info.paramInfo).filterMap fun (a, i) =>
          if i.binderInfo.isExplicit then some a else none
        if explicitArgs.size ≥ 2 then pairs := pairs.push (explicitArgs[0]!, explicitArgs[1]!)
      for (cand, defn) in pairs.flatMap (fun (a, b) => #[(a, b), (b, a)]) do
        unless cand.isFVar && xs.contains cand do continue
        let c := cand.fvarId!
        if defn.containsFVar c then continue
        let some target ← definitionIn? defn explicit? | continue
        -- the property: the hypotheses on the candidate, and for an iff the other side
        -- each with its binder when it is an instance argument, whose value later conditions use
        let mut props : Array (Expr × Option Expr) := #[]
        let pp (e : Expr) : MetaM String := return (← ppExpr e).pretty (width := 1000)
        -- Every binder other than the candidate is recorded, with no judgment of what matters: a
        -- hypothesis about the candidate is the property; any other hypothesis, and every instance
        -- argument, is an assumption, where the characterization holds; the rest are variables.
        let mut context : Array String := #[]
        let mut variables : Array String := #[]
        for x in xs do
          if x == cand then continue
          let ty ← inferType x
          let inst := (← x.fvarId!.getBinderInfo).isInstImplicit
          -- An instance argument about the candidate is part of the property: what a type
          -- characterized up to isomorphism has to be (`[ConditionallyCompleteLinearOrderedField K]`).
          if (← Meta.isProp ty) || inst then
            if ty.containsFVar c then props := props.push (ty, if inst then some x else none)
            else
              let s ← pp ty
              context := context.push (if inst then s!"[{s}]" else s)
          else variables := variables.push s!"{← x.fvarId!.getUserName} : {← pp ty}"
        if let some o := other? then props := props.push (o, none)
        if props.isEmpty then continue
        -- Where the definition is applied to something other than a variable of the theorem, the
        -- characterization covers that case only (the Bochner integral at `G := ℝ`). Instance
        -- arguments follow from the others and are not counted.
        let mut specialized : Array String := #[]
        if defn.getAppFn.constName? == some target then
          let dInfo ← getFunInfoNArgs defn.getAppFn defn.getAppNumArgs
          let names := (← getConstInfo target).type.getForallBinderNames
          for ((a, i), k) in (defn.getAppArgs.zip dInfo.paramInfo).zipIdx do
            if i.binderInfo.isInstImplicit then continue
            let a := (← instantiateMVars a).eta
            unless a.isFVar && xs.contains a do
              specialized := specialized.push s!"{names.getD k `_} := {← pp a}"
        let circular := props.any (·.1.getUsedConstants.contains target)
        -- existence: the definition in the candidate's place satisfies each condition
        let lemmas := lemmasFor target
        -- A premise may be assumed when it is a proposition about the theorem's own variables,
        -- fully determined, and not about the definition: a condition on its arguments.
        let ours := xs.map (·.fvarId!)
        let assumable (e : Expr) : MetaM Bool := do
          let e ← instantiateMVars e
          if e.hasMVar || e.hasAnyFVar (!ours.contains ·) then return false
          if e.getUsedConstants.contains target then return false
          Meta.isProp e
        let mut conditions := #[]
        -- The definition in the candidate's place, and for an instance condition the instance found
        -- for it in the binder's place: later conditions mention the earlier instances
        -- (`[IsStrictOrderedRing K]` depends on `[Field K]`).
        let mut subst : Array (Expr × Expr) := #[(cand, defn)]
        -- The theorem's universes, fitted to the definition's: a type characterized up to
        -- isomorphism is quantified over `K : Type u`, and `ℝ` lives in `Type`.
        let lvls ← levelParams.mapM fun _ => mkFreshLevelMVar
        let fit (e : Expr) : MetaM Expr := instantiateMVars (e.instantiateLevelParams levelParams lvls)
        discard <| isDefEq (← fit (← inferType cand)) (← inferType defn)
        for (pr, binder?) in props do
          -- the iff's other side follows from the theorem once `R (d …) (d …)` does
          let goalType ← fit ((if other?.isSome && pr == other?.get! then rel else pr).replaceFVars
            (subst.map (·.1)) (subst.map (·.2)))
          let proof ← match binder? with
            | some x =>
              match ← observing? (synthInstance goalType) with
              | some v => subst := subst.push (x, v); pure (some (#[], #[]))
              | none => pure none
            | none => withoutModifyingState do
              let g ← mkFreshExprMVar goalType
              proveFrom lemmas assumable 3 g.mvarId!
          let (used, assumed) := proof.getD (#[], #[])
          let mut assuming := #[]
          for a in assumed do
            let s ← pp a
            unless assuming.contains s do assuming := assuming.push s
          conditions := conditions.push
            { text := ← pp pr, proved := proof.isSome
              provedBy := used.toList.eraseDups.toArray, assuming }
        return some
          { form := if other?.isSome then "iff" else "uniqueness", target
            candidate := (← c.getUserName).toString
            -- with binder types: `∃ e : K ≃+*o ℝ, …` says what `e` is an isomorphism of
            relation := (← withOptions (Lean.pp.funBinderTypes.set · true) (ppExpr rel)).pretty (width := 1000)
            relationHead := inner.getAppFn.constName?.getD .anonymous
            conditions, context, variables, specialized, circular }
    return none

end TheoremForm

/-! ### The attribute -/

/--
`@[characterization property definition "why"]`, `@[characterization existence]` and
`@[characterization uniqueness]` mark the three parts of a claim that a definition is *the* object
with a given property: the predicate, the theorem that the definition satisfies it, and the
theorem that nothing else does — up to a relation read off that theorem's own conclusion.

```lean
@[characterization property entropy "the Shannon axioms"]
def IsEntropy (p : Distribution α) (h : ℝ) : Prop := …

@[characterization existence]
theorem isEntropy_entropy (p : Distribution α) : IsEntropy p (entropy p) := …

@[characterization uniqueness]
theorem IsEntropy.unique (h₁ : IsEntropy p x) (h₂ : IsEntropy p y) : x = y := …
```

With no keyword, `@[characterization]` goes on a theorem that states a characterization by itself,
with no predicate (see "A characterization stated by one theorem" above):

```lean
@[characterization "the defining equation"]
theorem eq_double_iff (n m : Nat) : m = double n ↔ m = n + n := …
```

With a keyword, the predicate on the two theorems is optional — by default it is
read off the statement — and can be given when the guess is wrong or ambiguous, as
`@[characterization uniqueness IsEntropy]`. A comment may follow in either position; on the
property it is the place to say what the characterization is *called*.

Unlike `@[specifies]`, the shapes are checked: a theorem whose statement is not what its role
claims is a build error, not a wrong entry in a published specification.
-/
syntax (name := characterization) (priority := high) &"characterization"
  (ppSpace (&"property" <|> &"existence" <|> &"uniqueness"))?
  (ppSpace ident)? (ppSpace str)? : attr

register_option characterization.checkExistence : Bool := {
  defValue := true
  descr := "warn when a theorem carrying `@[characterization]` has conditions that the definition \
    was not shown to satisfy from its `@[specifies]` theorems"
}

register_option characterization.checkNotCircular : Bool := {
  defValue := true
  descr := "warn when a predicate carrying `@[characterization property f]` mentions `f`, which \
    would make the characterization vacuous"
}

/-- The role named by `stx`.

Three shapes have to be read, because the same source text arrives differently depending on which
parser produced it: a `&"keyword"` in an alternation becomes a wrapper node of kind
`token.property`, a bare one becomes an atom (whose kind is its own text), and `Attr.simple` would
deliver an identifier. All three carry the word in the last component of the kind, or in the
identifier. -/
private def roleOf? (stx : Syntax) : Option CharRole :=
  let word :=
    if stx.isIdent then toString stx.getId
    else match stx.getKind with
      | .str _ s => s
      | _ => ""
  match word with
  | "property" => some .property
  | "existence" => some .existence
  | "uniqueness" => some .uniqueness
  | _ => none

initialize registerBuiltinAttribute {
  name := `characterization
  descr := "mark this declaration as one of the three parts of a characterization of a definition"
  applicationTime := .afterTypeChecking
  add := fun declName stx attrKind => do
    unless attrKind == .global do
      throwError "`characterization` must be a global attribute: a characterization is a claim \
        about the definition, not about a section or a namespace"

    -- `@[characterization existence]` is an identifier followed by one identifier, which is also
    -- exactly what `Attr.simple` accepts. `priority := high` should mean the parser above wins,
    -- but both shapes are handled so that a change in that resolution is not a silent failure.
    -- `Attr.simple` delivers its one argument as an identifier: a role keyword, or the definition
    -- of the keyword-less form.
    let (role?, hubStx?, commentStx?) :=
      if stx.getKind == ``Lean.Parser.Attr.simple then
        match stx[1].getOptional? with
        | some a => match roleOf? a with
          | some r => (some r, none, none)
          | none => (none, some a, none)
        | none => (none, none, none)
      else
        (stx[1].getOptional?.bind roleOf?, stx[2].getOptional?, stx[3].getOptional?)
    let comment := (commentStx?.bind Syntax.isStrLit?).getD ""

    let env ← getEnv
    let some info := env.find? declName
      | throwError "unknown declaration `{declName}`"

    let some role := role?
      | -- The keyword-less form: one theorem, no predicate.
        unless ← isProof info do
          throwError "`@[characterization]` belongs on a theorem that states a characterization, \
            but `{declName}` is not a proposition. On a predicate, write \
            `@[characterization property myDefinition]`"
        let explicit? ← hubStx?.mapM fun id => Elab.realizeGlobalConstNoOverloadWithInfo id
        let lemmasFor (target : Name) : Array Name :=
          (specTheoremsFor env target).filterMap fun e =>
            if e.theoremName == declName then none else some e.theoremName
        let some shape ← Meta.MetaM.run' (readTheorem info.type info.levelParams explicit? lemmasFor)
          | throwError "`{declName}` does not state a characterization. That would be either an \
              iff, `R x (definition …) ↔ property of x`, or a uniqueness theorem, \
              `hypotheses on x → R x (definition …)`, where `x` is a variable of the theorem and \
              `R` a relation applied to the two. Its statement is{indentExpr info.type}"
        let target := shape.target
        let some anchor := anchor? env declName target
          | throwError "cannot record that `{declName}` characterizes `{target}`: both are declared \
              in imported modules, so the entry would sit in a module neither of them points back \
              to and a consumer reaching either through its own imports would not see it. Write \
              the annotation in the module that declares one of them."
        if (charEntries env).any fun e => e.role == .theorem && e.declName == declName then
          throwError "`{declName}` is already registered as a characterization"
        if shape.circular && characterization.checkNotCircular.get (← getOptions) then
          logWarning m!"the property `{declName}` states about `{shape.candidate}` mentions \
            `{target}`, the definition it characterizes: a property that refers to the definition \
            pins nothing down. Set `characterization.checkNotCircular` to `false` to silence this."
        let open_ := shape.conditions.filter (!·.proved)
        if !open_.isEmpty && characterization.checkExistence.get (← getOptions) then
          logWarning m!"`{declName}` characterizes `{target}` only once `{target}` is shown to \
            satisfy its property, and these conditions were not shown from the `@[specifies \
            {target}]` theorems declared so far:\
            {MessageData.joinSep (open_.toList.map fun c => m!"\n  {c.text}") ""}\n\
            State them as `@[specifies]` theorems before this one, or apply the attribute after \
            them, as `attribute [characterization] {declName}`. Set \
            `characterization.checkExistence` to `false` to silence this."
        addEntry ({ declName, role := .theorem, property := declName, target
                    relation := shape.relation, relationHead := shape.relationHead, comment
                    form := shape.form, candidate := shape.candidate
                    conditions := shape.conditions, context := shape.context
                    variables := shape.variables, specialized := shape.specialized } : CharEntry).toEntry
          anchor
        unless (specEntries env).any fun e => e.theoremName == declName && e.target == target do
          addEntry ({ theoremName := declName, target, comment } : SpecEntry).toEntry anchor
        return

    if role == .property then
      if ← isProof info then
        throwError "`characterization property` belongs on a predicate, but `{declName}` is a \
          proof. The property is the statement a characterization is *about*; the theorem that \
          the definition satisfies it carries `@[characterization existence]`"
      let some hubStx := hubStx?
        | throwError "`@[characterization property]` needs the definition it characterizes, as \
            `@[characterization property myDefinition]`"
      let target ← Elab.realizeGlobalConstNoOverloadWithInfo hubStx
      if target == declName then
        throwError "`{declName}` cannot characterize itself"
      let some targetInfo := env.find? target
        | throwError "unknown declaration `{target}`"
      if ← isProof targetInfo then
        throwError "`{target}` is itself a proof, but `characterization property` names the \
          definition the annotated predicate is a property of"
      unless ← Meta.MetaM.run' (isPredicateOn declName target) do
        throwError "`{declName}` cannot characterize `{target}`: a characterizing property has to \
          land in `Prop` with a last argument of the type its definition has, or returns, so that \
          `{declName} … ({target} …)` is a proposition. Here the property is\
          {indentExpr info.type}\nand the definition is{indentExpr targetInfo.type}"
      let some anchor := anchor? env declName target
        | throwError "cannot record a characterization of `{target}` by `{declName}`: both are \
            declared in imported modules, so the entry would sit in a module neither of them \
            points back to and a consumer reaching either through its own imports would not see \
            it. Write the annotation in the module that declares one of them."
      if (charEntries env).any fun e =>
          e.role == .property && e.declName == declName && e.target == target then
        throwError "`{declName}` is already registered as a characterizing property of `{target}`"

      -- A property that refers to the definition it characterizes is satisfied by that definition
      -- for no reason at all, and pins nothing down. Nearly always a mistake, but only nearly —
      -- the reference can sit in a side condition that carries none of the content — so it is a
      -- warning, as the corresponding check on `@[specifies]` is.
      if characterization.checkNotCircular.get (← getOptions) then
        if (predicateUses info).contains target then
          logWarning m!"`{declName}` is marked as a characterizing property of `{target}`, but it \
            mentions `{target}`: a property that refers to the definition it characterizes pins \
            nothing down. Set `characterization.checkNotCircular` to `false` to silence this."

      addEntry ({ declName, role := .property, property := declName, target, comment } : CharEntry).toEntry
        anchor
    else
      unless ← isProof info do
        throwError "`characterization {role.keyword}` belongs on a theorem, but `{declName}` is \
          not a proposition"
      let pred ← match hubStx? with
        | some id => Elab.realizeGlobalConstNoOverloadWithInfo id
        | none =>
          match ← Meta.MetaM.run' (inferProperty env info.type role) with
          | some p => pure p
          | none =>
            throwError "cannot tell which characterizing property `{declName}` is part of: \
              nothing in its statement is registered with `@[characterization property]`. Name it \
              explicitly, as `@[characterization {role.keyword} MyProperty]`"
      let targets := characterizedBy env pred
      if targets.isEmpty then
        throwError "`{pred}` is not a characterizing property: mark it with \
          `@[characterization property theDefinition]` before naming it here"

      -- A predicate may characterize more than one definition, and this theorem belongs to
      -- exactly one of those bundles; which one is settled by the statement, not by the author.
      let mut found : Option (Name × String × Name) := none
      for target in targets do
        if found.isSome then continue
        if role == .existence then
          if ← Meta.MetaM.run' (statesExistence info.type pred target) then
            found := some (target, "", .anonymous)
        else
          if let some (rel, relHead) ← Meta.MetaM.run' (statesUniqueness info.type pred target) then
            found := some (target, rel, relHead)
      let some (target, relation, relationHead) := found
        | if role == .existence then
            throwError "`{declName}` does not state that {andList targets} satisfies `{pred}`: \
              that would be `{pred} … x`, with `x` built from the definition. Its statement is\
              {indentExpr info.type}"
          else
            throwError "`{declName}` does not state that `{pred}` determines its subject: that \
              would end in a relation between two objects its hypotheses say satisfy `{pred}`, \
              or between one such object and {andList targets}. Its statement is\
              {indentExpr info.type}"

      let some anchor := anchor? env declName target
        | throwError "cannot record that `{declName}` is the {role.keyword} part of the \
            characterization of `{target}`: both are declared in imported modules, so the entry \
            would sit in a module neither of them points back to and a consumer reaching either \
            through its own imports would not see it. Write the annotation in the module that \
            declares one of them."
      if (charEntries env).any fun e =>
          e.role == role && e.declName == declName && e.property == pred && e.target == target then
        throwError "`{declName}` is already registered as the {role.keyword} part of the \
          characterization of `{target}` by `{pred}`"

      addEntry ({ declName, role, property := pred, target, relation, relationHead, comment } :
        CharEntry).toEntry anchor
      -- A theorem of a characterization is a fortiori part of the specification of the
      -- definition, so it is recorded as one too — see the note on `specEntries` above. Skipped
      -- when the author also wrote `@[specifies]`, whose own duplicate check is an error.
      unless (specEntries env).any fun e => e.theoremName == declName && e.target == target do
        addEntry ({ theoremName := declName, target, comment } : SpecEntry).toEntry anchor
}

end TrustAnnotations
