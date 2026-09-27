module

public import TrustAnnotations.Test.Domain
meta import TrustAnnotations

@[expose] public section

/-!
# `@[domain]` across modules

A catalogue declares the domain of a definition it does not own, and reads the predicates of
another module: both have to work from outside the definition's module, since that is where the
tools and catalogues are.
-/

open Lean

namespace TrustAnnotations.Test.DomainCatalogue

-- A definition of Lean core, which this module cannot annotate at its declaration.
attribute [domain (fun n => 0 < n) "0 below the domain"] Nat.pred

/--
info: Nat.pred: fun n => 0 < n (catalogue, Nat.pred._domain) — 0 below the domain
TrustAnnotations.Test.Domain.sub': q ≤ p (author, TrustAnnotations.Test.Domain.sub'._domain) — truncated at 0 below the domain
-/
#guard_msgs in
#eval show CoreM Unit from do
  for d in [``Nat.pred, ``TrustAnnotations.Test.Domain.sub'] do
    let some e := TrustAnnotations.domainOf? (← getEnv) d | IO.println s!"{d}: none"
    IO.println s!"{e.decl}: {e.statement} ({e.source}, {e.predicate})\
      {if e.note.isEmpty then "" else s!" — {e.note}"}"

-- `@[up_to]` from a catalogue as well, on a definition of Lean core.
attribute [up_to (· % 2 = · % 2) "only its parity matters here"] Nat.succ

/--
info: Nat.succ: x % 2 = y % 2 (catalogue, Nat.succ._upTo)
-/
#guard_msgs in
#eval show CoreM Unit from do
  let some e := TrustAnnotations.upToOf? (← getEnv) ``Nat.succ | IO.println "none"
  IO.println s!"{e.decl}: {e.statement} ({e.source}, {e.relation})"

-- The imported module's hidden predicates keep their bodies, so they unfold here.
example : TrustAnnotations.Test.Domain.sub'._domain 3 2 := (by decide : 2 ≤ 3)
example : Nat.pred._domain 5 := (by decide : 0 < 5)

end TrustAnnotations.Test.DomainCatalogue
