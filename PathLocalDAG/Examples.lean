import PathLocalDAG.Fibers

/-!
# Three-vertex witnesses for incomparability with Markov equivalence
-/

namespace PathLocalDAG

def chain3Poset : FinitePoset 3 where
  le := fun x y => x.val ≤ y.val
  le_refl := fun x => Nat.le_refl x.val
  le_trans := fun _ _ _ => Nat.le_trans
  le_antisymm := by
    intro x y hxy hyx
    exact Fin.ext (Nat.le_antisymm hxy hyx)

/-- The reachability poset of 0 ← 1 → 2. -/
def fork3Poset : FinitePoset 3 where
  le := fun x y => x = y ∨ (x = 1 ∧ y ≠ 1)
  le_refl := fun x => Or.inl rfl
  le_trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | ⟨rfl, hy⟩
    · exact hyz
    rcases hyz with rfl | ⟨hyone, _⟩
    · exact Or.inr ⟨rfl, hy⟩
    · exact False.elim (hy hyone)
  le_antisymm := by
    intro x y hxy hyx
    rcases hxy with hxy | ⟨hx, hy⟩
    · exact hxy
    rcases hyx with hyx | ⟨hyone, _⟩
    · exact hyx.symm
    · exact False.elim (hy hyone)

def chain3Edges : EdgeSet 3 :=
  {(0, 1), (1, 2)}

def fork3Edges : EdgeSet 3 :=
  {(1, 0), (1, 2)}

def triangle3Edges : EdgeSet 3 :=
  {(0, 1), (1, 2), (0, 2)}

theorem chain3Edges_realizes : Realizes chain3Poset chain3Edges := by
  rw [realizes_iff_cover_subset_edges_subset_comparable]
  constructor
  · intro e he
    obtain ⟨x, y⟩ := e
    rw [mem_coverEdges] at he
    fin_cases x <;> fin_cases y <;>
      simp [Covers, chain3Poset, FinitePoset.LT, FinitePoset.LE,
        chain3Edges] at he ⊢
    all_goals
      have hmid := he (z := (1 : Fin 3)) (by decide) (by decide)
      omega
  · intro e he
    obtain ⟨x, y⟩ := e
    rw [mem_comparableEdges]
    fin_cases x <;> fin_cases y <;>
      simp [chain3Poset, FinitePoset.LT, FinitePoset.LE,
        chain3Edges] at he ⊢

theorem triangle3Edges_realizes : Realizes chain3Poset triangle3Edges := by
  rw [realizes_iff_cover_subset_edges_subset_comparable]
  constructor
  · intro e he
    obtain ⟨x, y⟩ := e
    rw [mem_coverEdges] at he
    fin_cases x <;> fin_cases y <;>
      simp [Covers, chain3Poset, FinitePoset.LT, FinitePoset.LE,
        triangle3Edges] at he ⊢
  · intro e he
    obtain ⟨x, y⟩ := e
    rw [mem_comparableEdges]
    fin_cases x <;> fin_cases y <;>
      simp [chain3Poset, FinitePoset.LT, FinitePoset.LE,
        triangle3Edges] at he ⊢

theorem fork3Edges_realizes : Realizes fork3Poset fork3Edges := by
  rw [realizes_iff_cover_subset_edges_subset_comparable]
  constructor
  · intro e he
    obtain ⟨x, y⟩ := e
    rw [mem_coverEdges] at he
    fin_cases x <;> fin_cases y <;>
      simp [Covers, fork3Poset, FinitePoset.LT, FinitePoset.LE,
        fork3Edges] at he ⊢
  · intro e he
    obtain ⟨x, y⟩ := e
    rw [mem_comparableEdges]
    fin_cases x <;> fin_cases y <;>
      simp [fork3Poset, FinitePoset.LT, FinitePoset.LE,
        fork3Edges] at he ⊢

noncomputable def chain3DAG : DAG 3 :=
  ReachabilityFiber.toDAG
    (⟨chain3Edges, chain3Edges_realizes⟩ : ReachabilityFiber chain3Poset)

noncomputable def fork3DAG : DAG 3 :=
  ReachabilityFiber.toDAG
    (⟨fork3Edges, fork3Edges_realizes⟩ : ReachabilityFiber fork3Poset)

noncomputable def triangle3DAG : DAG 3 :=
  ReachabilityFiber.toDAG
    (⟨triangle3Edges, triangle3Edges_realizes⟩ :
      ReachabilityFiber chain3Poset)

theorem fork3_atLeastTwoComparablePairs :
    AtLeastTwoComparablePairs fork3Poset := by
  let e : VertexPair 3 := ⟨(0, 1), by decide⟩
  let f : VertexPair 3 := ⟨(1, 2), by decide⟩
  refine ⟨e, f, ?_, ?_, ?_⟩
  · decide
  · right
    exact ⟨Or.inr ⟨rfl, by decide⟩, by decide⟩
  · left
    exact ⟨Or.inr ⟨rfl, by decide⟩, by decide⟩

theorem chain3_fork3_signature_ne :
    dagSignatureSet chain3DAG ≠ dagSignatureSet fork3DAG := by
  intro hsig
  have hChainReach : reachabilityPoset chain3DAG = chain3Poset := by
    unfold chain3DAG
    exact reachabilityPoset_fiber_toDAG _
  have hForkReach : reachabilityPoset fork3DAG = fork3Poset := by
    unfold fork3DAG
    exact reachabilityPoset_fiber_toDAG _
  have hpossig : fullSignatures fork3Poset = fullSignatures chain3Poset := by
    rw [← hForkReach, ← hChainReach]
    exact hsig.symm
  rcases (recovery_from_path_signatures fork3_atLeastTwoComparablePairs).1
      hpossig with hEq | hDual
  · have h01 : chain3Poset.LE 0 1 := by
      change (0 : Nat) ≤ 1
      decide
    rw [hEq] at h01
    simp [fork3Poset, FinitePoset.LE] at h01
  · have h12 : chain3Poset.LE 1 2 := by
      change (1 : Nat) ≤ 2
      decide
    rw [hDual] at h12
    simp [fork3Poset, FinitePoset.LE, FinitePoset.dual] at h12

theorem chain3_fork3_markovEquivalent :
    MarkovEquivalent chain3Edges fork3Edges := by
  constructor
  · ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [mem_skeleton_iff]
        simp [chain3Edges, fork3Edges]
        aesop
  · intro x z y
    fin_cases x <;> fin_cases z <;> fin_cases y <;>
      simp [IsUnshieldedCollider, chain3Edges, fork3Edges]

theorem chain3_triangle3_signature_eq :
    dagSignatureSet chain3DAG = dagSignatureSet triangle3DAG := by
  simpa [chain3DAG, triangle3DAG] using
    (fiber_signature_set_eq
      (⟨chain3Edges, chain3Edges_realizes⟩ : ReachabilityFiber chain3Poset)).trans
      (fiber_signature_set_eq
        (⟨triangle3Edges, triangle3Edges_realizes⟩ :
          ReachabilityFiber chain3Poset)).symm

theorem chain3_triangle3_not_markovEquivalent :
    ¬ MarkovEquivalent chain3Edges triangle3Edges := by
  apply not_markovEquivalent_of_skeleton_ne
  intro h
  have h02 : s((0 : Fin 3), (2 : Fin 3)) ∈ skeleton triangle3Edges := by
    rw [mem_skeleton_iff]
    simp [triangle3Edges]
  rw [← h, mem_skeleton_iff] at h02
  simp [chain3Edges] at h02

/-- Paper Proposition 4.1: signature equivalence and Markov equivalence are
incomparable. -/
theorem signature_and_markov_equivalence_incomparable :
    (∃ G H : DAG 3,
      MarkovEquivalent G.edges H.edges ∧
      dagSignatureSet G ≠ dagSignatureSet H) ∧
    (∃ G H : DAG 3,
      ¬ MarkovEquivalent G.edges H.edges ∧
      dagSignatureSet G = dagSignatureSet H) := by
  refine ⟨⟨chain3DAG, fork3DAG, ?_, chain3_fork3_signature_ne⟩,
    ⟨chain3DAG, triangle3DAG, ?_, chain3_triangle3_signature_eq⟩⟩
  · simpa [DAG.edges, chain3DAG, fork3DAG] using
      chain3_fork3_markovEquivalent
  · simpa [DAG.edges, chain3DAG, triangle3DAG] using
      chain3_triangle3_not_markovEquivalent

end PathLocalDAG
