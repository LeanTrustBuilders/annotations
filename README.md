# TrustAnnotations

Lean attributes that record information about declarations, all stored in **one generic
environment extension**, so a tool can read every attribute built on it, including ones defined after
the tool was released. Depends on Lean core only.

## Why one generic extension

A tool reading annotations out of a compiled project must have their extension registered in its own
process: imported entries are matched to registered extensions by name, and silently dropped
otherwise. With one extension per attribute, the tool would have to link every attribute package, and
each new attribute would need a new release of the tool for every toolchain. Here every attribute
writes `(attribute, declaration, payload)` entries, with a JSON payload, into the same extension; the
extractor links this package once and exports each attribute as a dataset facet.

## Attributes

| attribute | on | records |
|---|---|---|
| `@[claim]`, `@[claim "reference"]` | a theorem | one of the results the project puts forward, optionally with where it is stated informally |
| `@[example_of d]` | a theorem | a concrete object satisfies the definition `d`: `d` is not vacuous |
| `@[nonexample_of d]` | a theorem | a concrete object does *not* satisfy `d`: `d` is not trivially true |
| `@[specifies d "why"]` | a theorem | part of the specification of `d`: a property its author offers as evidence that `d` is the intended one. `d` may be omitted in `d`'s namespace; repeatable |
| `@[characterization "why"]`, `@[characterization d "why"]` | a theorem | the theorem characterizes a definition: an iff `R x (d …) ↔ property of x`, or a uniqueness theorem `hypotheses on x → R x (d …)` (below) |
| `@[characterization property d "why"]` | a predicate `P` | `d` is *the* object with property `P`, up to a relation, with `@[characterization existence]` (`d` satisfies `P`) and `@[characterization uniqueness]` (`P` determines its subject) on the theorems. For a property worth a name of its own |
| `@[up_to R "note"]` | a definition | what the definition is determined up to: a relation on its result type, with its arguments in scope (`@[up_to (· =ᵐ[μ] ·)]`). A statement that tells related values apart is about the representative chosen |
| `@[domain (proposition) "note"]` | a definition | where the definition is meant to apply: a proposition about its arguments (`@[domain (0 ≤ p ∧ 0 < q)]`), or a function of its explicit arguments (`@[domain (fun n => 0 < n)]`). Outside it, the value is a junk value or a convention |

`claim`, `example_of` and `nonexample_of` check that they are on a proposition, and apply once;
`example_of` and `nonexample_of` check that `d` is a definition and warn when the statement does not
mention it. `up_to` and `domain` also apply to a definition of another library
(`attribute [domain (0 < x)] Real.log`), for a catalogue.

```lean
def IsEven (n : Nat) : Prop := n % 2 = 0

@[example_of IsEven] theorem isEven_four : IsEven 4 := by unfold IsEven; decide
@[nonexample_of IsEven] theorem not_isEven_three : ¬ IsEven 3 := by unfold IsEven; decide

@[claim "Folklore, Proposition 1"]
theorem isEven_add {m n : Nat} (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  unfold IsEven at *; omega
```

### A characterization by one theorem

```lean
def double (n : Nat) : Nat := n + n

@[characterization "the defining equation"]
theorem eq_double_iff (n m : Nat) : m = double n ↔ m = n + n := …
```

The candidate `m` is a variable the theorem quantifies over, `double` is the definition (read off the
relation, or named: `@[characterization double]`), and `=` is the relation. For an iff, `double` has
the property by reflexivity. For a uniqueness theorem, each hypothesis on the candidate is shown for
the definition from its `@[specifies]` theorems declared before, with the theorem's other hypotheses
in context; a premise of a specification theorem that the context lacks is assumed and recorded
(`assuming`), as where the definition has the property. A condition nothing shows is recorded as
open, with a warning, and the characterization as incomplete; applying the attribute again later
picks up specification theorems declared in between.

A type can be characterized up to isomorphism the same way: the candidate is a type, its property its
instance arguments, and the relation an isomorphism type, possibly under `Nonempty`. The isomorphism
pins down only the structure its type names.

### Domains and relations

```lean
@[domain (0 ≤ p ∧ 0 < q) "0 · log (0 / q) = 0, by convention"]
noncomputable def klTerm (p q : ℝ) : ℝ := p * Real.log (p / q)
```

The domain is also stored as a hidden predicate over the definition's arguments (`klTerm._domain`), so
a tool can use the proposition itself; `domainEntries` and `domainOf?` read domains back. An `up_to`
relation is elaborated against what the definition returns after its arguments, stored as a hidden
declaration (`d._upTo`), and read back by `upToEntries` and `upToOf?`. Both record `source`:
`author` when declared in the definition's own module, `catalogue` otherwise.

## Use

```toml
# lakefile.toml
[[require]]
name = "TrustAnnotations"
git = "https://github.com/LeanTrustBuilders/annotations"
rev = "main"
```

A file using the module system writes `meta import TrustAnnotations` (attributes apply at compile
time); another writes `import TrustAnnotations`.

## Payloads

The payloads are the format: the extractor exports them as they are, in the `entries` of the facet
`annotation.<attribute>` (S2), and tools read them there.

| attribute | payload |
|---|---|
| `claim` | `{}`, or `{reference}` |
| `example_of`, `nonexample_of` | `{target}`: the definition |
| `specifies` | `{target, comment}` |
| `characterization` | `role` (`property`, `existence`, `uniqueness` or `theorem`), `property` (the predicate, or for `theorem` the theorem itself), `target` (the definition), `relation` (the uniqueness theorem's conclusion as written), `relationHead` (its head constant), `comment`. For `theorem`, also `form` (`iff` or `uniqueness`), `candidate`, `conditions` (each `{text, proved, by, assuming}`), `context` (every other assumption, as written), `variables`, `specialized` (arguments of the definition it fixes) and `complete` |
| `domain` | `{predicate, statement, note, source}`: the hidden predicate, the domain as written, the note, and `author` or `catalogue` |
| `up_to` | `{relation, statement, relationHead, note, source}`: the hidden relation, the relation applied to two variables, its head constant, the note, and `author` or `catalogue` |

**Versions of a payload.** A payload may carry `version`, the version of that attribute's payload;
without it, it is version 1. Within a version a payload only gains keys; a key whose meaning changes,
or goes, makes a new version, recorded in `version` and in this table. A reader ignores the keys it
does not know, and checks `version` before relying on one whose meaning has changed. Every payload
above is version 1.

## Reading annotations

`TrustAnnotations.entries env` returns every entry visible in `env`; `specEntries`, `charEntries` and
`characterizations` read specifications and characterizations back. A tool reading a compiled project
links this package and imports with `importModules (loadExts := true)` after
`enableInitializersExecution`.

## Defining a new attribute

```lean
syntax (name := my_attr) &"my_attr" (ppSpace str)? : attr

initialize
  TrustAnnotations.registerAnnotationAttribute `my_attr "what it records" fun decl stx => do
    -- check the application, then compute the payload
    return { payload := Lean.Json.mkObj [("note", "…")] }
```

The attribute is global and applied at most once per declaration, and the extractor exports it as the
facet `annotation.my_attr` unchanged. `TrustAnnotations.Entry` is two names and a string, and stays
so: its layout is part of the `.olean` format, read by tools that may link another version of this
package. Anything an attribute needs to evolve goes in its payload.

## Versions

`main` follows the newest Lean toolchain; a branch `lean-v<toolchain>` carries the same code on an
older one (`lean-v4.34.0`, `lean-v4.34.0-rc2`). The tags are older snapshots.

## Tests

`lake build TrustAnnotationsTest` checks the recorded entries, every rejection message, the warning,
and that entries are visible from an importing module.
