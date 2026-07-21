import PathLocalDAG.Basic

/-!
# Path signatures

An unoriented labeled Hamiltonian path is represented canonically as an
ordering paired with its reversal, modulo swapping the pair.
-/

namespace PathLocalDAG

/-- The reversal class of a labeled total order. This is the abstract
unoriented Hamiltonian path used in the paper. -/
abbrev PathSignature (n : ℕ) := Sym2 (VertexOrder n)

/-- The path signature of an ordering. -/
def signature {n : ℕ} (L : VertexOrder n) : PathSignature n :=
  s(L, L.reverse)

/-- Paper Lemma 2.2: a path signature determines its ordering up to reversal. -/
theorem signature_eq_iff_reverse {n : ℕ} (L M : VertexOrder n) :
    signature L = signature M ↔ M = L ∨ M = L.reverse := by
  constructor
  · intro h
    rcases Sym2.eq_iff.mp h with hsame | hswap
    · exact Or.inl hsame.1.symm
    · exact Or.inr hswap.2.symm
  · rintro (rfl | rfl)
    · rfl
    · simp only [signature, VertexOrder.reverse_reverse]
      exact Sym2.eq_swap

@[simp] theorem signature_reverse {n : ℕ} (L : VertexOrder n) :
    signature L.reverse = signature L := by
  exact (signature_eq_iff_reverse L.reverse L).2 (Or.inr (by simp))

/-- Full set of path signatures across all linear extensions. -/
def fullSignatures {n : ℕ} (P : FinitePoset n) : Set (PathSignature n) :=
  {τ | ∃ L : VertexOrder n, IsLinearExtension P L ∧ signature L = τ}

theorem signature_mem_fullSignatures {n : ℕ} {P : FinitePoset n}
    {L : VertexOrder n} (hL : IsLinearExtension P L) :
    signature L ∈ fullSignatures P :=
  ⟨L, hL, rfl⟩

theorem mem_fullSignatures_iff {n : ℕ} {P : FinitePoset n}
    {τ : PathSignature n} :
    τ ∈ fullSignatures P ↔
      ∃ L : VertexOrder n, IsLinearExtension P L ∧ signature L = τ :=
  Iff.rfl

/-- Global duality leaves the complete signature set unchanged. -/
theorem fullSignatures_dual {n : ℕ} (P : FinitePoset n) :
    fullSignatures P.dual = fullSignatures P := by
  ext τ
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨L.reverse, ?_, ?_⟩
    · intro x y hxy
      exact hL (x := y) (y := x) hxy
    · simp
  · rintro ⟨L, hL, rfl⟩
    refine ⟨L.reverse, ?_, ?_⟩
    · intro x y hxy
      exact hL (x := y) (y := x) hxy
    · simp

/-- Any reversal-invariant ordering functional is measurable with respect to
the path signature. -/
structure PathLocalFunctional (n : ℕ) (α : Type*) where
  toFun : VertexOrder n → α
  reverse_invariant : ∀ L, toFun L.reverse = toFun L

instance {n : ℕ} {α : Type*} : CoeFun (PathLocalFunctional n α)
    (fun _ => VertexOrder n → α) :=
  ⟨PathLocalFunctional.toFun⟩

/-- Paper Proposition 5.2, ordering-level statement. -/
theorem signature_measurability {n : ℕ} {α : Type*}
    (D : PathLocalFunctional n α) {L M : VertexOrder n}
    (h : signature L = signature M) : D L = D M := by
  rcases (signature_eq_iff_reverse L M).1 h with rfl | rfl
  · rfl
  · exact (D.reverse_invariant L).symm

/-- Paper Proposition 5.2, graph-aggregation statement. -/
theorem full_signature_aggregation_eq {n : ℕ} {α : Type*}
    (A : Set (PathSignature n) → α) {P Q : FinitePoset n}
    (h : fullSignatures P = fullSignatures Q) :
    A (fullSignatures P) = A (fullSignatures Q) :=
  congrArg A h

end PathLocalDAG
