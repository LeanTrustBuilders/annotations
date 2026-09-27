# TrustAnnotations

Lean attributes that record information about declarations, all stored in **one generic
environment extension** so that tools can read every attribute built on it, including ones defined
after the tool was released.

Depends on Lean core only. Part of the [LeanTrustBuilders](https://github.com/LeanTrustBuilders)
suite; see [the design notes](https://github.com/LeanTrustBuilders/design/tree/main/AI_initial_docs),
in particular `suite-design.md` §3.2.

## Why one generic extension

A tool that reads annotations out of a compiled project must have the extension it reads
registered in its own process: imported extension entries are matched to registered extensions by
name, and silently dropped otherwise. If each attribute had its own extension, the tool would have
to link every attribute package, and each new attribute would need a new release of the tool for
every Lean toolchain.

Here every attribute writes `(attribute, declaration, payload)` entries into the same extension,
with the payload as JSON text. The extractor links this package once and exports each attribute as
a dataset facet named after it.

## Attributes

| attribute | on | records |
|---|---|---|
| `@[claim]`, `@[claim "reference"]` | a theorem | this is one of the results the project puts forward, optionally with where it is stated informally (a paper and theorem number, a book section, a Wikidata item) |
| `@[example_of d]` | a theorem | this theorem states that a concrete object satisfies the definition `d`: evidence that `d` is not vacuous |
| `@[nonexample_of d]` | a theorem | this theorem states that a concrete object does *not* satisfy `d`: evidence that `d` is not trivially true |
| `@[specifies d "why"]` | a theorem | this theorem is part of the specification of the definition `d`: one of the properties its author offers as evidence that `d` is the intended one. `d` may be omitted when the theorem sits in `d`'s namespace; repeat the attribute for several definitions |
| `@[characterization "why"]`, `@[characterization d "why"]` | a theorem | this theorem characterizes a definition, with no predicate declared for it: an iff `R x (d …) ↔ property of x`, or a uniqueness theorem `hypotheses on x → R x (d …)` whose hypotheses are the property. `d` and `R` are read off the conclusion; that `d` satisfies the property is shown from its `@[specifies]` theorems (checked; see below) |
| `@[characterization property d "why"]` | a predicate `P` | `P` characterizes the definition `d`: `d` is *the* object with property `P`, up to a relation. For a property that is worth a name of its own; otherwise the form above needs no predicate |
| `@[characterization existence]` | a theorem | `d` satisfies `P` (checked, with `isDefEq`) |
| `@[characterization uniqueness]` | a theorem | `P` determines its subject up to a relation, read off the conclusion (checked) |
| `@[up_to R "note"]` | a definition | what the definition is determined up to: a relation on its result type, with its arguments in scope (`@[up_to (· =ᵐ[μ] ·)]`). Its value is one representative, and a statement that tells related values apart is about that representative. What proves it is a characterization whose uniqueness theorem ends in the relation. `attribute [up_to …] d` also works on a definition of another library |
| `@[domain (proposition) "note"]` | a definition | where the definition is meant to apply: a proposition about its arguments, under their own names (`@[domain (0 ≤ p ∧ 0 < q)]`), or a function of its explicit arguments (`@[domain (fun n => 0 < n)]`). Outside it, the value is a junk value or a convention. `attribute [domain …] d` also works on a definition of another library, for a catalogue |

`claim`, `example_of` and `nonexample_of` check that they are applied to a proposition, are global,
and are applied once.
`example_of` and `nonexample_of` check that `d` resolves to a definition and warn when the
statement does not mention it.

```lean
def IsEven (n : Nat) : Prop := n % 2 = 0

@[example_of IsEven] theorem isEven_four : IsEven 4 := by unfold IsEven; decide
@[nonexample_of IsEven] theorem not_isEven_three : ¬ IsEven 3 := by unfold IsEven; decide

@[claim "Folklore, Proposition 1"]
theorem isEven_add {m n : Nat} (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  unfold IsEven at *; omega
```

### A characterization with no predicate

```lean
def double (n : Nat) : Nat := n + n

@[characterization "the defining equation"]
theorem eq_double_iff (n m : Nat) : m = double n ↔ m = n + n := …
```

The theorem is the characterization: the candidate `m` is a variable it quantifies over, `double`
is the definition (read off the other side of the relation, or named as
`@[characterization double]`), and `=` is the relation. For an iff, `double` satisfies the
property by reflexivity of the relation. For a uniqueness theorem, each hypothesis on the candidate
is shown for the definition from its `@[specifies]` theorems declared before, applied a few deep, with
the theorem's other hypotheses in context. On Mathlib's conditional expectation, the three
hypotheses of `ae_eq_condExp_of_forall_setIntegral_eq` are shown this way from restatements of
`integrable_condExp`, `setIntegral_condExp` and `stronglyMeasurable_condExp`. A condition nothing
shows is recorded as open, with a warning, and the characterization as incomplete; applying the
attribute later (`attribute [characterization] thm`) picks up specification theorems declared in
between.

Existence often needs more than uniqueness: a specification theorem may have a premise the
characterization's context does not provide (`⟨M⟩` compensates `M²` only for a square-integrable
adapted `M`, while any two compensators agree without that). Such a premise is assumed, and
recorded with the condition (`assuming`) as where the definition has the property, so the
uniqueness theorem needs no hypothesis its own proof does not use. Only premises of specification
theorems can be assumed, never a condition itself, and only propositions about the theorem's own
variables that do not mention the definition.

The payload of such an entry has `role` `"theorem"`, the theorem as `property`, and also `form`
(`"iff"` or `"uniqueness"`), `candidate`, `conditions` (each `{text, proved, by, assuming}`), `specialized` (the definition's arguments the characterization fixes rather than quantifies over, `G := ℝ`: it covers that case only), `context` (every assumption of the theorem not about the candidate, as written: its other hypotheses and all its instance arguments, in brackets; nothing is left out, since a missing assumption would make the characterization look more general than it is), `variables` (its other binders) and `complete`.

A type can be characterized up to isomorphism the same way: the candidate is a type, its property
its instance arguments, and the relation an isomorphism type, possibly under `Nonempty`. Existence
finds the instances for the definition, in order, each fitted into the next:

```lean
@[characterization Real "the conditionally complete linearly ordered field"]
theorem real_orderRingIso (K : Type*) [Field K] [ConditionallyCompleteLinearOrder K]
    [IsStrictOrderedRing K] : Nonempty (K ≃+*o ℝ) := …
```

### Domains

```lean
@[domain (0 ≤ p ∧ 0 < q) "0 · log (0 / q) = 0, by convention"]
noncomputable def klTerm (p q : ℝ) : ℝ := p * Real.log (p / q)

attribute [domain (0 < x)] Real.log   -- in a catalogue module
```

The payload records the domain as written (`statement`), the `note`, `source` (`"author"` when
declared in the definition's own module, `"catalogue"` otherwise) and `predicate`: the domain is also
stored as a hidden predicate over the definition's arguments, `klTerm._domain`, so that a tool can
use the proposition itself. Its name is internal, so documentation, search and completion skip it,
and its body is exported under the module system. `domainEntries` and `domainOf?` read domains
back.

### What a definition is determined up to

```lean
attribute [up_to (· =ᵐ[μ] ·) "one version among the functions equal to it almost everywhere"]
  MeasureTheory.condExp   -- in a catalogue
```

The relation is elaborated against what the definition returns after its arguments. A definition
returning a function (`condExp … : α → E`) has more binders in its type than arguments, so the
arity is the deepest one the relation elaborates against. The relation is stored as a hidden
declaration, `condExp._upTo`, over the definition's arguments. The payload records it applied to two
variables (`statement`, `x =ᵐ[μ] y`), its head constant (`relationHead`, `Filter.EventuallyEq`),
the `note`, and the `source`. `upToEntries` and `upToOf?` read these back. A type determined up to
isomorphism is not covered: an isomorphism of fields is not a relation on bare types.

### Where these come from

`specifies` and `characterization` come from the `Characterization` package (earlier `LeanSpec`, in
`LeanMachineLearning/exposition`), moved here with their syntax, checks and tests unchanged
(`TrustAnnotations/Specification.lean`), so that one extension serves every annotation. A project
using them replaces `import Characterization` with `import TrustAnnotations` and requires this
package instead; nothing else changes. `specEntries`, `charEntries` and `characterizations` read
them back.

## Use

```toml
# lakefile.toml
[[require]]
name = "TrustAnnotations"
git = "https://github.com/LeanTrustBuilders/annotations"
rev = "main"
```

A file using the module system applies attributes at compile time, so it writes
`meta import TrustAnnotations`. A file not using the module system writes `import TrustAnnotations`.

## Defining a new attribute on the generic extension

```lean
syntax (name := my_attr) &"my_attr" (ppSpace str)? : attr

initialize
  TrustAnnotations.registerAnnotationAttribute `my_attr "what it records" fun decl stx => do
    -- check the application, then compute the payload
    return { payload := Lean.Json.mkObj [("note", "…")] }
```

The attribute is then global, applied at most once per declaration, and its entries are exported
by the extractor as the facet `annotation.my_attr` with no change to the extractor.

## Reading annotations

`TrustAnnotations.entries env` returns every entry visible in `env`. A tool reading a compiled
project must link this package and import with `importModules (loadExts := true)` after
`enableInitializersExecution`.

## Versions

`main` follows the newest Lean toolchain; a branch `lean-v<toolchain>` carries the same code on an
older one (`lean-v4.34.0`, `lean-v4.34.0-rc2`). The tags `v4.34.0-rc2`, `v4.34.0` and `v4.35.0-rc2`
are snapshots from before `specifies` and `characterization` moved here.

## Compatibility

`TrustAnnotations.Entry` is two names and a string, and it stays that way: its layout is part of
the `.olean` format, read by tools that may link a different version of this package than the
project was compiled against. Anything an attribute needs to evolve goes in its payload.

## Tests

`lake build TrustAnnotationsTest` checks the recorded entries, every rejection message, the
warning, and that entries are visible from an importing module.
