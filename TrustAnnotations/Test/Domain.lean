module

public import TrustAnnotations
meta import TrustAnnotations

@[expose] public section

/-!
# Tests for `@[domain]`

The attribute records where a definition is meant to apply, and stores the domain as a hidden
predicate over the definition's arguments. These tests read the entries back, use the hidden
predicate, and pin every rejection message. `DomainCatalogue.lean` covers the other side: a domain
declared for a definition of another module, and this module's predicates read from outside.

Run with `lake build TrustAnnotationsTest`.
-/

open Lean

namespace TrustAnnotations.Test.Domain

/-! ## Accepted forms -/

/-- Subtraction, meant for `q ≤ p`. -/
@[domain (q ≤ p) "truncated at 0 below the domain"]
def sub' (p q : Nat) : Nat := p - q

/-- The predecessor, defined by pattern matching, so its argument has no name to refer to. -/
@[domain (fun n => 0 < n)]
def pred' : Nat → Nat
  | 0 => 0
  | n + 1 => n

/-- The first element, with implicit and instance arguments, in any universe. -/
@[domain (xs ≠ [])]
def head' {α : Type u} [Inhabited α] (xs : List α) : α := xs.headD default

/-! ## Reading the annotations back -/

private def dump (env : Environment) : String :=
  let ours := (TrustAnnotations.domainEntries env).filter fun e =>
    (`TrustAnnotations.Test.Domain).isPrefixOf e.decl
  String.intercalate "\n" <| ours.toList.map fun e =>
    let note := if e.note.isEmpty then "" else s!" — {e.note}"
    s!"{e.decl}: {e.statement} ({e.source}, {e.predicate}){note}"

/--
info: TrustAnnotations.Test.Domain.sub': q ≤ p (author, TrustAnnotations.Test.Domain.sub'._domain) — truncated at 0 below the domain
TrustAnnotations.Test.Domain.pred': fun n => 0 < n (author, TrustAnnotations.Test.Domain.pred'._domain)
TrustAnnotations.Test.Domain.head': xs ≠ [] (author, TrustAnnotations.Test.Domain.head'._domain)
-/
#guard_msgs in
#eval show CoreM Unit from do IO.println (dump (← getEnv))

-- The hidden predicate takes the definition's arguments, with their binder infos and universes.
/--
info: TrustAnnotations.Test.Domain.head'._domain.{u} {α : Type u} [Inhabited α] (xs : List α) : Prop
-/
#guard_msgs in
#check head'._domain

example : sub'._domain 3 2 := (by decide : 2 ≤ 3)
example : pred'._domain 1 := (by decide : 0 < 1)
example : ¬ head'._domain ([] : List Nat) := fun h => h rfl

/-! ## Rejections and warnings -/

/--
error: `domain` belongs on a definition, but `TrustAnnotations.Test.Domain.sub'_le` is a proof: a theorem's hypotheses already say where it applies
-/
#guard_msgs in
@[domain (0 < p)]
theorem sub'_le (p q : Nat) : sub' p q ≤ p := Nat.sub_le p q

/--
error: `TrustAnnotations.Test.Domain.sub'` already has a declared domain, `q ≤ p`
-/
#guard_msgs in
attribute [domain (q < p)] sub'

/--
error: `domain` must be a global attribute: a domain is a claim about the definition, not about a section or a namespace
-/
#guard_msgs in
attribute [local domain (fun n => 0 < n)] pred'

/--
warning: the domain declared for `TrustAnnotations.Test.Domain.twice` mentions `TrustAnnotations.Test.Domain.twice` itself: a domain says which arguments the definition is meant for, so it is normally about the arguments alone
-/
#guard_msgs in
@[domain (twice n < 100)]
def twice (n : Nat) : Nat := 2 * n

end TrustAnnotations.Test.Domain
