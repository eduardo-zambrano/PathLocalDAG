import PathLocalDAG.Signatures
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Fintype.Sort

/-!
# Concrete path signatures

This file bridges the paper's concrete signature--the two endpoints and the
unordered set of consecutive vertex pairs--to the reversal-class
representation used by `PathLocalDAG.Signatures`.
-/

namespace PathLocalDAG

/-- A type synonym that equips the vertices with a specified `VertexOrder`
without replacing the ordinary numerical order on `Fin n`. -/
def OrderedVertex {n : ℕ} (_L : VertexOrder n) := Fin n
  deriving Fintype

namespace OrderedVertex

def toFin {n : ℕ} {L : VertexOrder n} : OrderedVertex L → Fin n :=
  fun x => x

def ofFin {n : ℕ} {L : VertexOrder n} : Fin n → OrderedVertex L :=
  fun x => x

@[simp] theorem toFin_ofFin {n : ℕ} {L : VertexOrder n} (x : Fin n) :
    toFin (L := L) (ofFin (L := L) x) = x := rfl

@[simp] theorem ofFin_toFin {n : ℕ} {L : VertexOrder n} (x : OrderedVertex L) :
    ofFin (L := L) (toFin x) = x := rfl

noncomputable instance instLinearOrder {n : ℕ} (L : VertexOrder n) :
    LinearOrder (OrderedVertex L) where
  le x y := L.LE (toFin x) (toFin y)
  lt x y := L.LE (toFin x) (toFin y) ∧ ¬L.LE (toFin y) (toFin x)
  le_refl x := L.le_refl (toFin x)
  le_trans _ _ _ hxy hyz := L.le_trans hxy hyz
  le_antisymm _ _ hxy hyx := by
    exact L.le_antisymm hxy hyx
  le_total x y := L.le_total (toFin x) (toFin y)
  toDecidableLE := Classical.decRel _
  toDecidableEq := Classical.decEq _
  toDecidableLT := Classical.decRel _

def equivFin {n : ℕ} (L : VertexOrder n) : OrderedVertex L ≃ Fin n where
  toFun := toFin
  invFun := ofFin
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

end OrderedVertex

namespace VertexOrder

/-- The vertices listed from first to last in the given order. -/
noncomputable def enumeration {n : ℕ} (L : VertexOrder n) : Equiv.Perm (Fin n) := by
  exact (Fintype.orderIsoFinOfCardEq (OrderedVertex L) (Fintype.card_fin n)).toEquiv.trans
    (OrderedVertex.equivFin L)

theorem enumeration_le_iff {n : ℕ} (L : VertexOrder n) (i j : Fin n) :
    i ≤ j ↔ L.LE (L.enumeration i) (L.enumeration j) := by
  change i ≤ j ↔
    (Fintype.orderIsoFinOfCardEq
      (OrderedVertex L) (Fintype.card_fin n)) i ≤
    (Fintype.orderIsoFinOfCardEq
      (OrderedVertex L) (Fintype.card_fin n)) j
  exact (Fintype.orderIsoFinOfCardEq
    (OrderedVertex L) (Fintype.card_fin n)).le_iff_le.symm

/-- Reversing a vertex order reverses its concrete enumeration. -/
noncomputable def reverseEnumerationOrderIso {n : ℕ} (L : VertexOrder n) :
    Fin n ≃o OrderedVertex L.reverse where
  toEquiv := Fin.revPerm.trans <|
    L.enumeration.trans (OrderedVertex.equivFin L.reverse).symm
  map_rel_iff' := by
    intro i j
    change L.LE (L.enumeration j.rev) (L.enumeration i.rev) ↔ i ≤ j
    rw [← L.enumeration_le_iff]
    exact Fin.rev_le_rev

theorem enumeration_reverse {n : ℕ} (L : VertexOrder n) (i : Fin n) :
    L.reverse.enumeration i = L.enumeration i.rev := by
  let canonical :=
    Fintype.orderIsoFinOfCardEq (OrderedVertex L.reverse) (Fintype.card_fin n)
  have h : canonical = reverseEnumerationOrderIso L := Subsingleton.elim _ _
  have hi := DFunLike.congr_fun h i
  exact congrArg OrderedVertex.toFin hi

end VertexOrder

/-- The two endpoint positions of the standard path on `Fin n`. This
definition also behaves uniformly for the empty and singleton cases. -/
def IsEndpointIndex {n : ℕ} (i : Fin n) : Prop :=
  (∀ j, i ≤ j) ∨ (∀ j, j ≤ i)

theorem isEndpointIndex_iff {k : ℕ} (i : Fin (k + 1)) :
    IsEndpointIndex i ↔ i = 0 ∨ i = Fin.last k := by
  constructor
  · rintro (hmin | hmax)
    · exact Or.inl (Fin.le_zero_iff'.1 (hmin 0))
    · exact Or.inr (Fin.last_le_iff.1 (hmax (Fin.last k)))
  · rintro (rfl | rfl)
    · exact Or.inl fun _ => Fin.zero_le _
    · exact Or.inr Fin.le_last

theorem isEndpointIndex_rev_iff {n : ℕ} (i : Fin n) :
    IsEndpointIndex i.rev ↔ IsEndpointIndex i := by
  constructor
  · rintro (hmin | hmax)
    · exact Or.inr fun j => Fin.rev_le_rev.mp (hmin j.rev)
    · exact Or.inl fun j => Fin.rev_le_rev.mp (hmax j.rev)
  · rintro (hmin | hmax)
    · exact Or.inr fun j => by simpa using Fin.rev_le_rev.mpr (hmin j.rev)
    · exact Or.inl fun j => by simpa using Fin.rev_le_rev.mpr (hmax j.rev)

theorem pathGraph_adj_rev_iff {n : ℕ} (i j : Fin n) :
    (SimpleGraph.pathGraph n).Adj i.rev j.rev ↔
      (SimpleGraph.pathGraph n).Adj i j := by
  change (i.rev ⋖ j.rev ∨ j.rev ⋖ i.rev) ↔ (i ⋖ j ∨ j ⋖ i)
  rw [show i.rev ⋖ j.rev ↔
      (OrderDual.toDual i : (Fin n)ᵒᵈ) ⋖ OrderDual.toDual j from
        Fin.revOrderIso.map_covBy,
    show j.rev ⋖ i.rev ↔
      (OrderDual.toDual j : (Fin n)ᵒᵈ) ⋖ OrderDual.toDual i from
        Fin.revOrderIso.map_covBy]
  simp only [toDual_covBy_toDual_iff]
  tauto

/-! ## Rigidity of a labeled path -/

theorem pathAutomorphism_eq_refl_of_zero {k : ℕ}
    (p : Equiv.Perm (Fin (k + 1)))
    (hadj : ∀ i j,
      (SimpleGraph.pathGraph (k + 1)).Adj (p i) (p j) ↔
        (SimpleGraph.pathGraph (k + 1)).Adj i j)
    (hzero : p 0 = 0) : p = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  generalize hm : i.val = m
  induction m using Nat.strong_induction_on generalizing i with
  | h m ih =>
      by_cases hm0 : m = 0
      · have hi0 : i = 0 := by
          apply Fin.ext
          simp [hm, hm0]
        simpa [hi0] using hzero
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        let a : Fin (k + 1) := ⟨m - 1, by omega⟩
        have ha_lt : a.val < m := by simp [a]; omega
        have hpa : p a = a := ih a.val ha_lt a rfl
        have hai : (SimpleGraph.pathGraph (k + 1)).Adj a i := by
          apply SimpleGraph.pathGraph_adj.mpr
          left
          simp [a]
          omega
        have hpai : (SimpleGraph.pathGraph (k + 1)).Adj a (p i) := by
          rw [← hpa]
          exact (hadj a i).mpr hai
        rcases SimpleGraph.pathGraph_adj.mp hpai with hforward | hbackward
        · apply Fin.ext
          change (p i).val = i.val
          simp [a] at hforward
          omega
        · by_cases hm1 : m = 1
          · simp [a, hm1] at hbackward
          · have hm2 : 2 ≤ m := by omega
            let b : Fin (k + 1) := ⟨m - 2, by omega⟩
            have hb_lt : b.val < m := by simp [b]; omega
            have hpb : p b = b := ih b.val hb_lt b rfl
            have hpib : p i = b := by
              apply Fin.ext
              simp [a, b] at hbackward ⊢
              omega
            have hib : i = b := p.injective (hpib.trans hpb.symm)
            have := congrArg Fin.val hib
            simp [b] at this
            omega

/-- Every automorphism of a finite path that sends an endpoint to an endpoint
is either the identity or reversal. -/
theorem pathAutomorphism_eq_refl_or_rev {k : ℕ}
    (p : Equiv.Perm (Fin (k + 1)))
    (hadj : ∀ i j,
      (SimpleGraph.pathGraph (k + 1)).Adj (p i) (p j) ↔
        (SimpleGraph.pathGraph (k + 1)).Adj i j)
    (hendpoint : IsEndpointIndex (p 0)) :
    p = Equiv.refl _ ∨ p = Fin.revPerm := by
  rcases (isEndpointIndex_iff (p 0)).mp hendpoint with hzero | hlast
  · exact Or.inl (pathAutomorphism_eq_refl_of_zero p hadj hzero)
  · right
    let q : Equiv.Perm (Fin (k + 1)) := p.trans Fin.revPerm
    have qadj : ∀ i j,
        (SimpleGraph.pathGraph (k + 1)).Adj (q i) (q j) ↔
          (SimpleGraph.pathGraph (k + 1)).Adj i j := by
      intro i j
      exact (pathGraph_adj_rev_iff (p i) (p j)).trans (hadj i j)
    have qzero : q 0 = 0 := by simp [q, hlast]
    have hq : q = Equiv.refl _ :=
      pathAutomorphism_eq_refl_of_zero q qadj qzero
    apply Equiv.ext
    intro i
    have hi := DFunLike.congr_fun hq i
    have hirev := congrArg Fin.rev hi
    simpa [q] using hirev

/-- The paper's concrete path signature: its endpoint set and its unordered
set of consecutive labeled pairs. -/
structure ConcretePathSignature (n : ℕ) where
  endpoints : Set (Fin n)
  consecutivePairs : Set (Sym2 (Fin n))

@[ext] theorem ConcretePathSignature.ext {n : ℕ}
    {σ τ : ConcretePathSignature n}
    (hendpoints : σ.endpoints = τ.endpoints)
    (hpairs : σ.consecutivePairs = τ.consecutivePairs) : σ = τ := by
  cases σ
  cases τ
  simp_all

/-- Relabel the endpoint positions and edges of the standard path by the
vertices' order of appearance. -/
noncomputable def concreteSignature {n : ℕ} (L : VertexOrder n) :
    ConcretePathSignature n where
  endpoints := {x | ∃ i, IsEndpointIndex i ∧ L.enumeration i = x}
  consecutivePairs :=
    {e | ∃ i j, (SimpleGraph.pathGraph n).Adj i j ∧
      s(L.enumeration i, L.enumeration j) = e}

@[simp] theorem concreteSignature_reverse {n : ℕ} (L : VertexOrder n) :
    concreteSignature L.reverse = concreteSignature L := by
  apply ConcretePathSignature.ext
  · ext x
    constructor
    · rintro ⟨i, hi, hix⟩
      refine ⟨i.rev, (isEndpointIndex_rev_iff i).2 hi, ?_⟩
      simpa [VertexOrder.enumeration_reverse] using hix
    · rintro ⟨i, hi, hix⟩
      refine ⟨i.rev, (isEndpointIndex_rev_iff i).2 hi, ?_⟩
      simpa [VertexOrder.enumeration_reverse] using hix
  · ext e
    constructor
    · rintro ⟨i, j, hij, he⟩
      refine ⟨i.rev, j.rev, (pathGraph_adj_rev_iff i j).2 hij, ?_⟩
      simpa [VertexOrder.enumeration_reverse] using he
    · rintro ⟨i, j, hij, he⟩
      refine ⟨i.rev, j.rev, (pathGraph_adj_rev_iff i j).2 hij, ?_⟩
      simpa [VertexOrder.enumeration_reverse] using he

theorem enumeration_pair_mem_consecutivePairs_iff {n : ℕ}
    (L : VertexOrder n) (i j : Fin n) :
    s(L.enumeration i, L.enumeration j) ∈
        (concreteSignature L).consecutivePairs ↔
      (SimpleGraph.pathGraph n).Adj i j := by
  constructor
  · rintro ⟨a, b, hab, hpair⟩
    rcases Sym2.eq_iff.mp hpair.symm with hsame | hswap
    · have hi : i = a := L.enumeration.injective hsame.1
      have hj : j = b := L.enumeration.injective hsame.2
      simpa [hi, hj] using hab
    · have hi : i = b := L.enumeration.injective hswap.1
      have hj : j = a := L.enumeration.injective hswap.2
      simpa [hi, hj] using hab.symm
  · intro hij
    exact ⟨i, j, hij, rfl⟩

theorem enumeration_mem_endpoints_iff {n : ℕ}
    (L : VertexOrder n) (i : Fin n) :
    L.enumeration i ∈ (concreteSignature L).endpoints ↔ IsEndpointIndex i := by
  constructor
  · rintro ⟨j, hj, heq⟩
    have hji : j = i := L.enumeration.injective heq
    simpa [hji] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem VertexOrder.eq_of_enumeration_eq {n : ℕ} {L M : VertexOrder n}
    (h : L.enumeration = M.enumeration) : L = M := by
  apply VertexOrder.ext
  intro x y
  obtain ⟨i, rfl⟩ := L.enumeration.surjective x
  obtain ⟨j, rfl⟩ := L.enumeration.surjective y
  exact (L.enumeration_le_iff i j).symm.trans <| by
    simpa [← h] using M.enumeration_le_iff i j

/-- Concrete rigidity: the endpoint-and-edge signature determines a nonempty
vertex order up to global reversal. This is the paper's concrete Lemma 2.2. -/
theorem concreteSignature_eq_iff_reverse {k : ℕ}
    (L M : VertexOrder (k + 1)) :
    concreteSignature L = concreteSignature M ↔
      M = L ∨ M = L.reverse := by
  constructor
  · intro hconcrete
    let p : Equiv.Perm (Fin (k + 1)) :=
      M.enumeration.trans L.enumeration.symm
    have hp_apply (i : Fin (k + 1)) :
        L.enumeration (p i) = M.enumeration i := by
      simp [p]
    have hpairs := congrArg ConcretePathSignature.consecutivePairs hconcrete
    have hendpoints := congrArg ConcretePathSignature.endpoints hconcrete
    have hadj : ∀ i j,
        (SimpleGraph.pathGraph (k + 1)).Adj (p i) (p j) ↔
          (SimpleGraph.pathGraph (k + 1)).Adj i j := by
      intro i j
      calc
        (SimpleGraph.pathGraph (k + 1)).Adj (p i) (p j) ↔
            s(L.enumeration (p i), L.enumeration (p j)) ∈
              (concreteSignature L).consecutivePairs :=
          (enumeration_pair_mem_consecutivePairs_iff L (p i) (p j)).symm
        _ ↔ s(M.enumeration i, M.enumeration j) ∈
              (concreteSignature M).consecutivePairs := by
          rw [hp_apply i, hp_apply j, hpairs]
        _ ↔ (SimpleGraph.pathGraph (k + 1)).Adj i j :=
          enumeration_pair_mem_consecutivePairs_iff M i j
    have hzeroEndpoint : IsEndpointIndex (0 : Fin (k + 1)) :=
      (isEndpointIndex_iff 0).mpr (Or.inl rfl)
    have hMendpoint : M.enumeration 0 ∈
        (concreteSignature M).endpoints :=
      (enumeration_mem_endpoints_iff M 0).mpr hzeroEndpoint
    have hLendpoint : M.enumeration 0 ∈
        (concreteSignature L).endpoints := by
      rw [hendpoints]
      exact hMendpoint
    have hpEndpoint : IsEndpointIndex (p 0) :=
      (enumeration_mem_endpoints_iff L (p 0)).mp <| by
        simpa [hp_apply 0] using hLendpoint
    rcases pathAutomorphism_eq_refl_or_rev p hadj hpEndpoint with hp | hp
    · left
      apply VertexOrder.eq_of_enumeration_eq
      apply Equiv.ext
      intro i
      have hpi := DFunLike.congr_fun hp i
      calc
        M.enumeration i = L.enumeration (p i) := (hp_apply i).symm
        _ = L.enumeration i := by rw [hpi]; rfl
    · right
      apply VertexOrder.eq_of_enumeration_eq
      apply Equiv.ext
      intro i
      calc
        M.enumeration i = L.enumeration (p i) := (hp_apply i).symm
        _ = L.enumeration i.rev := by rw [DFunLike.congr_fun hp i]; rfl
        _ = L.reverse.enumeration i := (L.enumeration_reverse i).symm
  · rintro (rfl | rfl)
    · rfl
    · exact (concreteSignature_reverse L).symm

/-- The concrete endpoint-and-edge representation carries exactly the same
information as the reversal-class representation used downstream. -/
theorem concreteSignature_eq_iff_signature_eq {k : ℕ}
    (L M : VertexOrder (k + 1)) :
    concreteSignature L = concreteSignature M ↔ signature L = signature M :=
  (concreteSignature_eq_iff_reverse L M).trans
    (signature_eq_iff_reverse L M).symm

/-- Full set of concrete endpoint-and-edge signatures across all linear
extensions. -/
noncomputable def fullConcreteSignatures {n : ℕ} (P : FinitePoset n) :
    Set (ConcretePathSignature n) :=
  {τ | ∃ L : VertexOrder n,
    IsLinearExtension P L ∧ concreteSignature L = τ}

theorem concreteSignature_mem_fullConcreteSignatures {n : ℕ}
    {P : FinitePoset n} {L : VertexOrder n} (hL : IsLinearExtension P L) :
    concreteSignature L ∈ fullConcreteSignatures P :=
  ⟨L, hL, rfl⟩

/-- Equality of full concrete signature sets is equivalent to equality of the
abstract reversal-class sets used by the recovery and fiber theorems. -/
theorem fullConcreteSignatures_eq_iff_fullSignatures_eq {k : ℕ}
    (P Q : FinitePoset (k + 1)) :
    fullConcreteSignatures P = fullConcreteSignatures Q ↔
      fullSignatures P = fullSignatures Q := by
  constructor
  · intro hconcrete
    apply Set.Subset.antisymm
    · rintro τ ⟨L, hL, rfl⟩
      have hmem : concreteSignature L ∈ fullConcreteSignatures P :=
        concreteSignature_mem_fullConcreteSignatures hL
      rw [hconcrete] at hmem
      rcases hmem with ⟨M, hM, hML⟩
      refine ⟨M, hM, ?_⟩
      exact (concreteSignature_eq_iff_signature_eq M L).mp hML
    · rintro τ ⟨L, hL, rfl⟩
      have hmem : concreteSignature L ∈ fullConcreteSignatures Q :=
        concreteSignature_mem_fullConcreteSignatures hL
      rw [← hconcrete] at hmem
      rcases hmem with ⟨M, hM, hML⟩
      refine ⟨M, hM, ?_⟩
      exact (concreteSignature_eq_iff_signature_eq M L).mp hML
  · intro habstract
    apply Set.Subset.antisymm
    · rintro τ ⟨L, hL, rfl⟩
      have hmem : signature L ∈ fullSignatures P :=
        signature_mem_fullSignatures hL
      rw [habstract] at hmem
      rcases hmem with ⟨M, hM, hML⟩
      refine ⟨M, hM, ?_⟩
      exact (concreteSignature_eq_iff_signature_eq M L).mpr hML
    · rintro τ ⟨L, hL, rfl⟩
      have hmem : signature L ∈ fullSignatures Q :=
        signature_mem_fullSignatures hL
      rw [← habstract] at hmem
      rcases hmem with ⟨M, hM, hML⟩
      refine ⟨M, hM, ?_⟩
      exact (concreteSignature_eq_iff_signature_eq M L).mpr hML

end PathLocalDAG
