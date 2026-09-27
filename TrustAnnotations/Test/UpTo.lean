module

public import TrustAnnotations
meta import TrustAnnotations

@[expose] public section

/-!
# Tests for `@[up_to]`

The attribute records what a definition is determined up to, a relation on its result type, and
stores it as a hidden declaration. These tests read the entries back, use the hidden relation, and
pin the attribute's own messages.

Run with `lake build TrustAnnotationsTest`.
-/

open Lean

namespace TrustAnnotations.Test.UpTo

/-! ## Accepted forms -/

/-- `n` rounded down to a multiple of `k`: any number of the same block of `k` would do. The
relation uses the definition's own argument `k`, and is an equation without being equality. -/
@[up_to (fun a b => a / k = b / k) "any number in the same block of k numbers"]
def roundDown (n k : Nat) : Nat := n / k * k

/-- A representative of the parity of `n`, with the `·` notation. -/
@[up_to (· % 2 = · % 2)]
def parityRep (n : Nat) : Nat := n % 2

/-- A function determined only away from `0`. -/
@[up_to (fun f g => ∀ n, 0 < n → f n = g n)]
def awayFromZero (f : Nat → Nat) : Nat → Nat := fun n => if n = 0 then 0 else f n

/-! ## Reading the annotations back -/

private def dump (env : Environment) : String :=
  let ours := (TrustAnnotations.upToEntries env).filter fun e =>
    (`TrustAnnotations.Test.UpTo).isPrefixOf e.decl
  String.intercalate "\n" <| ours.toList.map fun e =>
    let note := if e.note.isEmpty then "" else s!" — {e.note}"
    let head := if e.relationHead.isAnonymous then "-" else e.relationHead.toString
    s!"{e.decl}: up to {e.statement} [{head}] ({e.source}, {e.relation}){note}"

/--
info: TrustAnnotations.Test.UpTo.roundDown: up to a / k = b / k [Eq] (author, TrustAnnotations.Test.UpTo.roundDown._upTo) — any number in the same block of k numbers
TrustAnnotations.Test.UpTo.parityRep: up to x % 2 = y % 2 [Eq] (author, TrustAnnotations.Test.UpTo.parityRep._upTo)
TrustAnnotations.Test.UpTo.awayFromZero: up to ∀ (n : Nat), 0 < n → x n = y n [-] (author, TrustAnnotations.Test.UpTo.awayFromZero._upTo)
-/
#guard_msgs in
#eval show CoreM Unit from do IO.println (dump (← getEnv))

-- The hidden relation takes the definition's arguments, then two values of its result type.
/--
info: TrustAnnotations.Test.UpTo.roundDown._upTo (n k : Nat) : Nat → Nat → Prop
-/
#guard_msgs in
#check roundDown._upTo

example : roundDown._upTo 7 3 6 8 := (rfl : 6 / 3 = 8 / 3)

/-! ## Rejections and warnings -/

/--
error: `up_to` belongs on a definition, but `TrustAnnotations.Test.UpTo.roundDown_le` is a proof
-/
#guard_msgs in
@[up_to (· = ·)]
theorem roundDown_le (n k : Nat) : roundDown n k ≤ n := Nat.div_mul_le_self n k

/--
error: `TrustAnnotations.Test.UpTo.parityRep` is already declared to be determined up to `x % 2 = y % 2`
-/
#guard_msgs in
attribute [up_to (· = ·)] parityRep

/--
error: `up_to` must be a global attribute: it is a claim about the definition, not about a section or a namespace
-/
#guard_msgs in
attribute [local up_to (· = ·)] roundDown

/--
warning: `TrustAnnotations.Test.UpTo.exactly` is declared to be determined up to equality, which every definition is: the declaration says nothing
-/
#guard_msgs in
@[up_to (· = ·)]
def exactly (n : Nat) : Nat := n

end TrustAnnotations.Test.UpTo
