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
| `@[characterization property d "why"]` | a predicate `P` | `P` characterizes the definition `d`: `d` is *the* object with property `P`, up to a relation |
| `@[characterization existence]` | a theorem | `d` satisfies `P` (checked, with `isDefEq`) |
| `@[characterization uniqueness]` | a theorem | `P` determines its subject up to a relation, read off the conclusion (checked) |

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
