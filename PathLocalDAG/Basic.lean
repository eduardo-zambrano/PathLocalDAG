import Mathlib.Order.Extension.Linear
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-!
# Finite posets and labeled total orders

This file supplies paper-faithful finite objects without importing the
historical testing API. Vertices are labeled by Fin n.
-/

namespace PathLocalDAG

/-- A partial order on the labeled vertex set Fin n. -/
structure FinitePoset (n : ℕ) where
  le : Fin n → Fin n → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ ⦃x y z⦄, le x y → le y z → le x z
  le_antisymm : ∀ ⦃x y⦄, le x y → le y x → x = y

namespace FinitePoset

/-- The non-strict comparison relation of a finite poset. -/
def LE {n : ℕ} (P : FinitePoset n) (x y : Fin n) : Prop :=
  P.le x y

/-- The strict comparison relation of a finite poset. -/
def LT {n : ℕ} (P : FinitePoset n) (x y : Fin n) : Prop :=
  P.LE x y ∧ x ≠ y

theorem lt_irrefl {n : ℕ} (P : FinitePoset n) (x : Fin n) : ¬ P.LT x x := by
  simp [LT]

theorem lt_trans {n : ℕ} (P : FinitePoset n) {x y z : Fin n}
    (hxy : P.LT x y) (hyz : P.LT y z) : P.LT x z := by
  refine ⟨P.le_trans hxy.1 hyz.1, ?_⟩
  intro hxz
  subst z
  exact hyz.2 (P.le_antisymm hyz.1 hxy.1)

/-- Global order reversal. -/
def dual {n : ℕ} (P : FinitePoset n) : FinitePoset n where
  le := fun x y => P.LE y x
  le_refl := P.le_refl
  le_trans := fun _ _ _ hxy hyz => P.le_trans hyz hxy
  le_antisymm := fun _ _ hxy hyx => P.le_antisymm hyx hxy

@[simp] theorem dual_le {n : ℕ} (P : FinitePoset n) (x y : Fin n) :
    P.dual.LE x y ↔ P.LE y x := Iff.rfl

@[simp] theorem dual_lt {n : ℕ} (P : FinitePoset n) (x y : Fin n) :
    P.dual.LT x y ↔ P.LT y x := by
  constructor
  · rintro ⟨h, hne⟩
    exact ⟨h, Ne.symm hne⟩
  · rintro ⟨h, hne⟩
    exact ⟨h, Ne.symm hne⟩

@[ext] theorem ext {n : ℕ} {P Q : FinitePoset n}
    (h : ∀ x y, P.LE x y ↔ Q.LE x y) : P = Q := by
  cases P with
  | mk ple pr pt pa =>
      cases Q with
      | mk qle qr qt qa =>
          have hle : ple = qle := by
            funext x y
            exact propext (h x y)
          subst qle
          rfl

@[simp] theorem dual_dual {n : ℕ} (P : FinitePoset n) : P.dual.dual = P := by
  ext x y
  rfl

end FinitePoset

/-- A labeled total order on Fin n. -/
structure VertexOrder (n : ℕ) where
  le : Fin n → Fin n → Prop
  le_refl : ∀ x, le x x
  le_trans : ∀ ⦃x y z⦄, le x y → le y z → le x z
  le_antisymm : ∀ ⦃x y⦄, le x y → le y x → x = y
  le_total : ∀ x y, le x y ∨ le y x

namespace VertexOrder

/-- Non-strict precedence in a labeled total order. -/
def LE {n : ℕ} (L : VertexOrder n) (x y : Fin n) : Prop :=
  L.le x y

/-- Strict precedence in a labeled total order. -/
def Before {n : ℕ} (L : VertexOrder n) (x y : Fin n) : Prop :=
  L.LE x y ∧ x ≠ y

theorem before_iff_not_le {n : ℕ} (L : VertexOrder n) {x y : Fin n} :
    L.Before x y ↔ ¬ L.LE y x := by
  constructor
  · rintro ⟨hxy, hne⟩ hyx
    exact hne (L.le_antisymm hxy hyx)
  · intro h
    exact ⟨(L.le_total x y).resolve_right h, fun hxy => h (hxy ▸ L.le_refl y)⟩

theorem before_asymm {n : ℕ} (L : VertexOrder n) {x y : Fin n}
    (hxy : L.Before x y) : ¬ L.Before y x := by
  intro hyx
  exact hxy.2 (L.le_antisymm hxy.1 hyx.1)

@[ext] theorem ext {n : ℕ} {L M : VertexOrder n}
    (h : ∀ x y, L.LE x y ↔ M.LE x y) : L = M := by
  cases L with
  | mk lle lr lt la ltot =>
      cases M with
      | mk mle mr mt ma mtot =>
          have hle : lle = mle := by
            funext x y
            exact propext (h x y)
          subst mle
          rfl

/-- Reverse every comparison in a labeled total order. -/
def reverse {n : ℕ} (L : VertexOrder n) : VertexOrder n where
  le := fun x y => L.LE y x
  le_refl := L.le_refl
  le_trans := fun _ _ _ hxy hyz => L.le_trans hyz hxy
  le_antisymm := fun _ _ hxy hyx => L.le_antisymm hyx hxy
  le_total := fun x y => L.le_total y x

@[simp] theorem reverse_le {n : ℕ} (L : VertexOrder n) (x y : Fin n) :
    L.reverse.LE x y ↔ L.LE y x := Iff.rfl

@[simp] theorem reverse_before {n : ℕ} (L : VertexOrder n) (x y : Fin n) :
    L.reverse.Before x y ↔ L.Before y x := by
  exact FinitePoset.dual_lt
    ({ le := L.le, le_refl := L.le_refl, le_trans := L.le_trans,
       le_antisymm := L.le_antisymm } : FinitePoset n) x y

@[simp] theorem reverse_reverse {n : ℕ} (L : VertexOrder n) :
    L.reverse.reverse = L := by
  ext x y
  rfl

end VertexOrder

/-- L extends every comparison in P. -/
def IsLinearExtension {n : ℕ} (P : FinitePoset n) (L : VertexOrder n) : Prop :=
  ∀ ⦃x y⦄, P.LE x y → L.LE x y

theorem IsLinearExtension.before_of_lt {n : ℕ} {P : FinitePoset n}
    {L : VertexOrder n} (hL : IsLinearExtension P L) {x y : Fin n}
    (hxy : P.LT x y) : L.Before x y :=
  ⟨hL hxy.1, hxy.2⟩

theorem isLinearExtension_reverse_iff {n : ℕ} (P : FinitePoset n)
    (L : VertexOrder n) :
    IsLinearExtension P.dual L.reverse ↔ IsLinearExtension P L := by
  constructor <;> intro h x y hxy
  · exact h (x := y) (y := x) hxy
  · exact h (x := y) (y := x) hxy

/-- A noncomputable linear extension supplied by Szpilrajn's theorem. -/
noncomputable def someLinearExtension {n : ℕ} (P : FinitePoset n) :
    VertexOrder n := by
  letI : IsPartialOrder (Fin n) P.LE :=
    { refl := P.le_refl
      trans := fun _ _ _ hxy hyz => P.le_trans hxy hyz
      antisymm := fun _ _ hxy hyx => P.le_antisymm hxy hyx }
  let extension := (extend_partialOrder P.LE).choose
  let spec := (extend_partialOrder P.LE).choose_spec
  exact
    { le := extension
      le_refl := spec.1.1.1.1.1
      le_trans := spec.1.1.1.2.1
      le_antisymm := spec.1.1.2.1
      le_total := spec.1.2.1 }

theorem someLinearExtension_isExtension {n : ℕ} (P : FinitePoset n) :
    IsLinearExtension P (someLinearExtension P) := by
  letI : IsPartialOrder (Fin n) P.LE :=
    { refl := P.le_refl
      trans := fun _ _ _ hxy hyz => P.le_trans hxy hyz
      antisymm := fun _ _ hxy hyx => P.le_antisymm hxy hyx }
  intro x y hxy
  exact (extend_partialOrder P.LE).choose_spec.2 x y hxy

theorem exists_linearExtension {n : ℕ} (P : FinitePoset n) :
    ∃ L : VertexOrder n, IsLinearExtension P L :=
  ⟨someLinearExtension P, someLinearExtension_isExtension P⟩

end PathLocalDAG
