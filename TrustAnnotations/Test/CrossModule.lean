module

public import TrustAnnotations.Test.Basic
meta import TrustAnnotations.Test.Basic

@[expose] public section

/-!
# Annotations survive an import

What a tool reads is the state of an environment that *imports* the annotated modules, so the
entries of `TrustAnnotations.Test.Basic` must be visible here, alongside the ones this module adds.
-/

open Lean

namespace TrustAnnotations.Test.CrossModule

@[claim "added downstream"]
theorem isEven_ten : TrustAnnotations.Test.IsEven 10 := by unfold TrustAnnotations.Test.IsEven; decide

/-- info: imported: 6, local: 1 -/
#guard_msgs in
#eval show MetaM Unit from do
  let es := TrustAnnotations.entries (← getEnv)
  let imported := es.filter (·.decl.getPrefix == `TrustAnnotations.Test)
  let here := es.filter (·.decl.getPrefix == `TrustAnnotations.Test.CrossModule)
  logInfo m!"imported: {imported.size}, local: {here.size}"

end TrustAnnotations.Test.CrossModule
