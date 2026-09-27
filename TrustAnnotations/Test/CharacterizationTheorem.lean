module

public import TrustAnnotations
meta import TrustAnnotations

@[expose] public section

/-!
# Tests for `@[characterization]` with no keyword

A characterization stated by one theorem, with no predicate declared for it: an iff, or a
uniqueness theorem whose hypotheses on the candidate are the property. The attribute reads the
definition and the relation off the conclusion, and shows that the definition satisfies the
property: by reflexivity for an iff, from the definition's `@[specifies]` theorems for a uniqueness
theorem. As in `Characterization.lean`, the recorded entries are compared verbatim and every
rejection message is pinned.

Run with `lake build TrustAnnotationsTest`.
-/

open Lean

namespace TrustAnnotations.Test.CharacterizationTheorem

/-! ## Accepted forms -/

/-- Twice `n`. -/
def double (n : Nat) : Nat := n + n

-- An iff: both halves at once. The definition satisfies the property because `=` is reflexive.
@[characterization "the defining equation"]
theorem eq_double_iff (n m : Nat) : m = double n ↔ m = n + n := by
  unfold double; exact Iff.rfl

/-- Three times `n`. -/
def triple (n : Nat) : Nat := n + n + n

@[specifies]
theorem triple.sub (n : Nat) : triple n - n = n + n := by unfold triple; omega

@[specifies]
theorem triple.le (n : Nat) : n ≤ triple n := by unfold triple; omega

-- A uniqueness theorem, the candidate on the left: its two hypotheses on `m` are the property, and
-- `triple` satisfies them by the two `@[specifies]` theorems above.
@[characterization]
theorem eq_triple (n m : Nat) (h₁ : m - n = n + n) (h₂ : n ≤ m) : m = triple n := by
  unfold triple; omega

/-- `a` and `b` leave the same remainder mod 2. -/
def SameParity (a b : Nat) : Prop := a % 2 = b % 2

@[refl]
theorem SameParity.refl (a : Nat) : SameParity a a := rfl

/-- The number four. -/
def four : Nat := 4

-- A relation other than `=`, the candidate on the right, a hypothesis that is not about the
-- candidate (recorded as the context), and an explicitly named definition.
@[characterization four "determines a number only up to parity"]
theorem four_sameParity (n : Nat) (_h : 0 < four) (hn : n % 2 = 0) : SameParity four n := by
  unfold SameParity four; omega

/-- Four times `n`. -/
def quad (n : Nat) : Nat := 4 * n

@[specifies]
theorem quad.dvd (n : Nat) : 4 ∣ quad n := ⟨n, rfl⟩

-- Incomplete: nothing shows `quad n / 4 = n` yet, so the characterization is recorded as such.
/--
warning: `TrustAnnotations.Test.CharacterizationTheorem.eq_quad` characterizes `TrustAnnotations.Test.CharacterizationTheorem.quad` only once `TrustAnnotations.Test.CharacterizationTheorem.quad` is shown to satisfy its property, and these conditions were not shown from the `@[specifies TrustAnnotations.Test.CharacterizationTheorem.quad]` theorems declared so far:
  m / 4 = n
State them as `@[specifies]` theorems before this one, or apply the attribute after them, as `attribute [characterization] TrustAnnotations.Test.CharacterizationTheorem.eq_quad`. Set `characterization.checkExistence` to `false` to silence this.
-/
#guard_msgs in
@[characterization]
theorem eq_quad (n m : Nat) (h₁ : 4 ∣ m) (h₂ : m / 4 = n) : m = quad n := by
  obtain ⟨k, rfl⟩ := h₁; unfold quad; omega

/-- `f n + 1`. -/
def bump (f : Nat → Nat) (n : Nat) : Nat := f n + 1

@[specifies]
theorem bump.one_lt (hf : ∀ k, 0 < f k) (n : Nat) : 1 < bump f n := by
  have := hf n; unfold bump; omega

-- A premise of a specification theorem that is a hypothesis of the characterization as it stands,
-- a `∀`: it is found by assumption, before its binders are introduced.
@[characterization]
theorem eq_bump (f : Nat → Nat) (_hf : ∀ k, 0 < f k) (n m : Nat) (_h₁ : 1 < m) (h₂ : m = f n + 1) :
    m = bump f n := h₂

/-- `f n`, meant for a positive `f`. -/
def pick (f : Nat → Nat) (n : Nat) : Nat := f n

@[specifies]
theorem pick.pos (hf : ∀ k, 0 < f k) (n : Nat) : 0 < pick f n := hf n

-- Uniqueness needs nothing about `f`, existence needs `hf`: the theorem does not carry it, and
-- the premise of `pick.pos` is assumed and recorded instead.
@[characterization]
theorem eq_pick (f : Nat → Nat) (n m : Nat) (_h₁ : 0 < m) (h₂ : m = f n) : m = pick f n := h₂

@[specifies]
theorem pick.lt (h : pick f n < 5) : pick f n < 10 := by omega

-- A premise about the definition's own value is not assumed: that would be assuming the
-- property, not a condition on the arguments.
/--
warning: `TrustAnnotations.Test.CharacterizationTheorem.eq_pick'` characterizes `TrustAnnotations.Test.CharacterizationTheorem.pick` only once `TrustAnnotations.Test.CharacterizationTheorem.pick` is shown to satisfy its property, and these conditions were not shown from the `@[specifies TrustAnnotations.Test.CharacterizationTheorem.pick]` theorems declared so far:
  m < 10
State them as `@[specifies]` theorems before this one, or apply the attribute after them, as `attribute [characterization] TrustAnnotations.Test.CharacterizationTheorem.eq_pick'`. Set `characterization.checkExistence` to `false` to silence this.
-/
#guard_msgs in
@[characterization]
theorem eq_pick' (f : Nat → Nat) (n m : Nat) (_h₁ : m < 10) (h₂ : m = f n) : m = pick f n := h₂

/-- A proposition about a number, as a class. -/
class IsPos (n : Nat) : Prop where
  pos : 0 < n

/-- A proposition about a type, as a class. -/
class Small (α : Type) : Prop

/-- Half of `n`. -/
def half (n : Nat) : Nat := n / 2

-- Every assumption is recorded as where the characterization holds, the instance arguments too,
-- whatever they are about: `[Small α]` as well as `[IsPos n]`.
@[characterization]
theorem eq_half (α : Type) [Small α] (n m : Nat) [IsPos n] (h : m = n / 2) : m = half n := h

/-! ### A type determined up to isomorphism -/

/-- An isomorphism of types, as Lean core has none. -/
structure Iso (α β : Type) where
  to : α → β
  of : β → α
  to_of : ∀ b, to (of b) = b
  of_to : ∀ a, of (to a) = a

/-- Being a type with exactly two elements, as structure. -/
class IsTwo (K : Type) where
  iso : Iso K Bool

/-- The type with two elements. -/
def Two : Type := Bool

instance : IsTwo Two := ⟨⟨id, id, fun _ => rfl, fun _ => rfl⟩⟩

-- The candidate is a type, its property the instance argument `[IsTwo K]`, and the relation an
-- isomorphism type; `Two` has the property because the instance is found.
@[characterization "the type with two elements"]
theorem two_iso (K : Type) [IsTwo K] : Nonempty (Iso K Two) := ⟨IsTwo.iso⟩

/-! ### A characterization of a special case -/

/-- `(a, a)`, in any type. -/
def diag (α : Type) (a : α) : α × α := (a, a)

-- It characterizes `diag` at `α := Nat` only: recorded as such.
@[characterization]
theorem eq_diag_nat (a : Nat) (p : Nat × Nat) (h₁ : p.1 = a) (h₂ : p.2 = a) : p = diag Nat a := by
  cases p; simp_all [diag]

/-! ## Reading the annotations back -/

private def dump (env : Environment) : String :=
  let ours := (TrustAnnotations.characterizations env).filter fun c =>
    (`TrustAnnotations.Test.CharacterizationTheorem).isPrefixOf c.property
  String.intercalate "\n" <| ours.toList.map fun c =>
    let e := c.uniqueness[0]!
    let comment := if c.comment.isEmpty then "" else s!" — {c.comment}"
    let conds := e.conditions.toList.map fun k =>
      let how := if !k.proved then "open"
        else if k.provedBy.isEmpty then "shown"
        else s!"by {String.intercalate ", " (k.provedBy.toList.map toString)}"
      let assuming := if k.assuming.isEmpty then ""
        else s!" (assuming {String.intercalate ", " k.assuming.toList})"
      s!"    {k.text}: {how}{assuming}"
    String.intercalate "\n" <|
      [ s!"{c.target} by {c.property}{comment}",
        s!"  {e.form}, candidate {e.candidate}, up to: {e.relation} [{e.relationHead}]" ] ++
      conds ++
      (if e.context.isEmpty then [] else [s!"  where: {String.intercalate ", " e.context.toList}"]) ++
      (if e.specialized.isEmpty then [] else [s!"  only for: {String.intercalate ", " e.specialized.toList}"]) ++
      [ s!"  complete: {c.isComplete}" ]

/--
info: TrustAnnotations.Test.CharacterizationTheorem.double by TrustAnnotations.Test.CharacterizationTheorem.eq_double_iff — the defining equation
  iff, candidate m, up to: m = double n [Eq]
    m = n + n: shown
  complete: true
TrustAnnotations.Test.CharacterizationTheorem.triple by TrustAnnotations.Test.CharacterizationTheorem.eq_triple
  uniqueness, candidate m, up to: m = triple n [Eq]
    m - n = n + n: by TrustAnnotations.Test.CharacterizationTheorem.triple.sub
    n ≤ m: by TrustAnnotations.Test.CharacterizationTheorem.triple.le
  complete: true
TrustAnnotations.Test.CharacterizationTheorem.four by TrustAnnotations.Test.CharacterizationTheorem.four_sameParity — determines a number only up to parity
  uniqueness, candidate n, up to: SameParity four n [TrustAnnotations.Test.CharacterizationTheorem.SameParity]
    n % 2 = 0: shown
  where: 0 < four
  complete: true
TrustAnnotations.Test.CharacterizationTheorem.quad by TrustAnnotations.Test.CharacterizationTheorem.eq_quad
  uniqueness, candidate m, up to: m = quad n [Eq]
    4 ∣ m: by TrustAnnotations.Test.CharacterizationTheorem.quad.dvd
    m / 4 = n: open
  complete: false
TrustAnnotations.Test.CharacterizationTheorem.bump by TrustAnnotations.Test.CharacterizationTheorem.eq_bump
  uniqueness, candidate m, up to: m = bump f n [Eq]
    1 < m: by TrustAnnotations.Test.CharacterizationTheorem.bump.one_lt
    m = f n + 1: shown
  where: ∀ (k : Nat), 0 < f k
  complete: true
TrustAnnotations.Test.CharacterizationTheorem.pick by TrustAnnotations.Test.CharacterizationTheorem.eq_pick
  uniqueness, candidate m, up to: m = pick f n [Eq]
    0 < m: by TrustAnnotations.Test.CharacterizationTheorem.pick.pos (assuming ∀ (k : Nat), 0 < f k)
    m = f n: shown
  complete: true
TrustAnnotations.Test.CharacterizationTheorem.pick by TrustAnnotations.Test.CharacterizationTheorem.eq_pick'
  uniqueness, candidate m, up to: m = pick f n [Eq]
    m < 10: open
    m = f n: shown
  complete: false
TrustAnnotations.Test.CharacterizationTheorem.half by TrustAnnotations.Test.CharacterizationTheorem.eq_half
  uniqueness, candidate m, up to: m = half n [Eq]
    m = n / 2: shown
  where: [Small α], [IsPos n]
  complete: true
TrustAnnotations.Test.CharacterizationTheorem.Two by TrustAnnotations.Test.CharacterizationTheorem.two_iso — the type with two elements
  uniqueness, candidate K, up to: Nonempty (Iso K Two) [TrustAnnotations.Test.CharacterizationTheorem.Iso]
    IsTwo K: shown
  complete: true
TrustAnnotations.Test.CharacterizationTheorem.diag by TrustAnnotations.Test.CharacterizationTheorem.eq_diag_nat
  uniqueness, candidate p, up to: p = diag Nat a [Eq]
    p.fst = a: shown
    p.snd = a: shown
  only for: α := Nat
  complete: true
-/
#guard_msgs in
#eval show CoreM Unit from do IO.println (dump (← getEnv))

-- The rest of the context: the variables the characterization is about.
/--
info: #[α : Type, n : Nat]
-/
#guard_msgs in
#eval show CoreM Unit from do
  let some e := (TrustAnnotations.charEntries (← getEnv)).find?
    (·.declName == `TrustAnnotations.Test.CharacterizationTheorem.eq_half) | IO.println "none"
  IO.println e.variables

-- Each characterization theorem is also part of its definition's specification.
/--
info: #[TrustAnnotations.Test.CharacterizationTheorem.eq_double_iff]
-/
#guard_msgs in
#eval show CoreM Unit from do
  IO.println ((TrustAnnotations.specTheoremsFor (← getEnv)
    `TrustAnnotations.Test.CharacterizationTheorem.double).map (·.theoremName))

/-! ## Rejections and warnings -/

/--
error: `@[characterization]` belongs on a theorem that states a characterization, but `TrustAnnotations.Test.CharacterizationTheorem.notATheorem` is not a proposition. On a predicate, write `@[characterization property myDefinition]`
-/
#guard_msgs in
@[characterization]
def notATheorem : Nat := 0

-- Neither side of the relation is a variable of the theorem: this specifies `double`, it does not
-- characterize it.
/--
error: `TrustAnnotations.Test.CharacterizationTheorem.double_eq` does not state a characterization. That would be either an iff, `R x (definition …) ↔ property of x`, or a uniqueness theorem, `hypotheses on x → R x (definition …)`, where `x` is a variable of the theorem and `R` a relation applied to the two. Its statement is
  ∀ (n : Nat), double n = n + n
-/
#guard_msgs in
@[characterization]
theorem double_eq (n : Nat) : double n = n + n := rfl

-- The definition named does not appear where the relation needs it.
/--
error: `TrustAnnotations.Test.CharacterizationTheorem.eq_triple'` does not state a characterization. That would be either an iff, `R x (definition …) ↔ property of x`, or a uniqueness theorem, `hypotheses on x → R x (definition …)`, where `x` is a variable of the theorem and `R` a relation applied to the two. Its statement is
  ∀ (n m : Nat), m - n = n + n → n ≤ m → m = triple n
-/
#guard_msgs in
@[characterization double]
theorem eq_triple' (n m : Nat) (h₁ : m - n = n + n) (h₂ : n ≤ m) : m = triple n :=
  eq_triple n m h₁ h₂

-- A property that mentions the definition pins nothing down.
/--
warning: the property `TrustAnnotations.Test.CharacterizationTheorem.circular` states about `m` mentions `TrustAnnotations.Test.CharacterizationTheorem.double`, the definition it characterizes: a property that refers to the definition pins nothing down. Set `characterization.checkNotCircular` to `false` to silence this.
-/
#guard_msgs in
@[characterization]
theorem circular (n m : Nat) (h : m = double n) : m = double n := h

/--
error: `TrustAnnotations.Test.CharacterizationTheorem.eq_double_iff` is already registered as a characterization
-/
#guard_msgs in
attribute [characterization] eq_double_iff

end TrustAnnotations.Test.CharacterizationTheorem
