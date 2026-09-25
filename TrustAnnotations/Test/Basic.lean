module

public import TrustAnnotations
-- Attributes are applied at compile time, and the checks below read the extension from inside
-- `#eval`, which is compile-time too; both need the package at that level.
meta import TrustAnnotations

@[expose] public section

/-!
# Tests for the attributes of `TrustAnnotations`

The entries written here are read back verbatim, and every rejection is pinned with `#guard_msgs`:
these messages are the whole user interface of the attributes.

Run with `lake build TrustAnnotationsTest`.
-/

open Lean

namespace TrustAnnotations.Test

def IsEven (n : Nat) : Prop := n % 2 = 0

@[example_of IsEven]
theorem isEven_four : IsEven 4 := by unfold IsEven; decide

@[nonexample_of IsEven]
theorem not_isEven_three : ¬ IsEven 3 := by unfold IsEven; decide

@[claim "Folklore, Proposition 1"]
theorem isEven_add {m n : Nat} (hm : IsEven m) (hn : IsEven n) : IsEven (m + n) := by
  unfold IsEven at *
  omega

@[claim]
theorem isEven_zero : IsEven 0 := by unfold IsEven; decide

theorem later : IsEven 2 := by unfold IsEven; decide

attribute [example_of IsEven] later

/--
info: claim TrustAnnotations.Test.isEven_add {"reference":"Folklore, Proposition 1"}
claim TrustAnnotations.Test.isEven_zero {}
example_of TrustAnnotations.Test.isEven_four {"target":"TrustAnnotations.Test.IsEven"}
example_of TrustAnnotations.Test.later {"target":"TrustAnnotations.Test.IsEven"}
nonexample_of TrustAnnotations.Test.not_isEven_three {"target":"TrustAnnotations.Test.IsEven"}
-/
#guard_msgs in
#eval show MetaM Unit from do
  let es := (entries (← getEnv)).filter (·.decl.getPrefix == `TrustAnnotations.Test)
  let es := es.qsort fun a b => a.attr.toString < b.attr.toString ||
    (a.attr == b.attr && a.decl.toString < b.decl.toString)
  logInfo m!"{"\n".intercalate (es.toList.map fun e => s!"{e.attr} {e.decl} {e.payload}")}"

/-! ## Rejections -/

/-- error: `claim` belongs on a theorem, but `TrustAnnotations.Test.notAProp` is not a proposition -/
#guard_msgs in
@[claim] def notAProp : Nat := 3

/-- error: `TrustAnnotations.Test.isEven_zero` already carries `@[claim]` -/
#guard_msgs in
attribute [claim] isEven_zero

/--
error: `TrustAnnotations.Test.isEven_four` is a proof, but `example_of` names the definition that `TrustAnnotations.Test.isEven_six` is an example of
-/
#guard_msgs in
@[example_of isEven_four] theorem isEven_six : IsEven 6 := by unfold IsEven; decide

/--
error: `claim` must be a global attribute: an annotation is a claim about the declaration, not about a section or a namespace
-/
#guard_msgs in
@[local claim] theorem isEven_eight : IsEven 8 := by unfold IsEven; decide

/-- error: `example_of` belongs on a theorem, but `TrustAnnotations.Test.four` is not a proposition -/
#guard_msgs in
@[example_of IsEven] def four : Nat := 4

/-! ## Warnings -/

/--
warning: `TrustAnnotations.Test.unrelated` is marked `@[example_of TrustAnnotations.Test.IsEven]`, but its statement does not mention `TrustAnnotations.Test.IsEven`
-/
#guard_msgs in
@[example_of IsEven] theorem unrelated : 2 + 2 = 4 := rfl

end TrustAnnotations.Test
