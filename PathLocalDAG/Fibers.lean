import PathLocalDAG.Recovery
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# DAG reachability and exact fibers

Finite directed graphs are represented by finite sets of ordered pairs.  A
graph in a reachability fiber is automatically acyclic, because its nonempty
paths are precisely the strict comparisons of a partial order.
-/

namespace PathLocalDAG

abbrev EdgeSet (n : ℕ) := Finset (Fin n × Fin n)

def EdgeRel {n : ℕ} (E : EdgeSet n) (x y : Fin n) : Prop :=
  (x, y) ∈ E

/-- Existence of a nonempty directed path. -/
def Reach {n : ℕ} (E : EdgeSet n) (x y : Fin n) : Prop :=
  Relation.TransGen (EdgeRel E) x y

/-- A graph realizes P when its nonempty reachability relation is the strict
order of P. -/
def Realizes {n : ℕ} (P : FinitePoset n) (E : EdgeSet n) : Prop :=
  ∀ x y, Reach E x y ↔ P.LT x y

theorem acyclic_of_realizes {n : ℕ} {P : FinitePoset n} {E : EdgeSet n}
    (h : Realizes P E) (x : Fin n) : ¬ Reach E x x := by
  rw [h]
  exact P.lt_irrefl x

/-- The oriented cover relation of P. -/
def Covers {n : ℕ} (P : FinitePoset n) (x y : Fin n) : Prop :=
  P.LT x y ∧ ∀ ⦃z⦄, P.LT x z → ¬ P.LT z y

theorem covers_lt {n : ℕ} {P : FinitePoset n} {x y : Fin n}
    (h : Covers P x y) : P.LT x y := h.1

theorem lt_iff_transGen_covers {n : ℕ} (P : FinitePoset n)
    {x y : Fin n} :
    P.LT x y ↔ Relation.TransGen (Covers P) x y := by
  classical
  letI : PartialOrder (Fin n) :=
    { le := P.LE
      lt := P.LT
      le_refl := P.le_refl
      le_trans := fun _ _ _ hxy hyz => P.le_trans hxy hyz
      le_antisymm := fun _ _ hxy hyx => P.le_antisymm hxy hyx
      lt_iff_le_not_ge := by
        intro a b
        constructor
        · rintro ⟨hab, hne⟩
          exact ⟨hab, fun hba => hne (P.le_antisymm hab hba)⟩
        · rintro ⟨hab, hnba⟩
          exact ⟨hab, fun heq => hnba (heq ▸ P.le_refl b)⟩ }
  letI : LocallyFiniteOrder (Fin n) := Fintype.toLocallyFiniteOrder
  simpa only [Covers] using
    (lt_iff_transGen_covBy (α := Fin n) (x := x) (y := y))

noncomputable def comparableEdges {n : ℕ} (P : FinitePoset n) : EdgeSet n := by
  classical
  exact Finset.univ.filter fun e => P.LT e.1 e.2

noncomputable def coverEdges {n : ℕ} (P : FinitePoset n) : EdgeSet n := by
  classical
  exact Finset.univ.filter fun e => Covers P e.1 e.2

noncomputable def optionalEdges {n : ℕ} (P : FinitePoset n) : EdgeSet n :=
  comparableEdges P \ coverEdges P

@[simp] theorem mem_comparableEdges {n : ℕ} {P : FinitePoset n}
    {e : Fin n × Fin n} : e ∈ comparableEdges P ↔ P.LT e.1 e.2 := by
  classical
  simp [comparableEdges]

@[simp] theorem mem_coverEdges {n : ℕ} {P : FinitePoset n}
    {e : Fin n × Fin n} : e ∈ coverEdges P ↔ Covers P e.1 e.2 := by
  classical
  simp [coverEdges]

@[simp] theorem mem_optionalEdges {n : ℕ} {P : FinitePoset n}
    {e : Fin n × Fin n} : e ∈ optionalEdges P ↔
      P.LT e.1 e.2 ∧ ¬ Covers P e.1 e.2 := by
  classical
  simp [optionalEdges]

theorem coverEdges_subset_comparableEdges {n : ℕ} (P : FinitePoset n) :
    coverEdges P ⊆ comparableEdges P := by
  intro e he
  rw [mem_comparableEdges]
  exact covers_lt (mem_coverEdges.mp he)

/-- Paper Theorem 4.2, exact sandwich characterization. -/
theorem realizes_iff_cover_subset_edges_subset_comparable {n : ℕ}
    (P : FinitePoset n) (E : EdgeSet n) :
    Realizes P E ↔ coverEdges P ⊆ E ∧ E ⊆ comparableEdges P := by
  constructor
  · intro h
    constructor
    · intro e he
      have hcover : Covers P e.1 e.2 := mem_coverEdges.mp he
      have hreach : Reach E e.1 e.2 := (h _ _).2 hcover.1
      cases hreach with
      | single hedge => exact hedge
      | tail hab hbc =>
          exfalso
          have hac : P.LT e.1 _ := (h _ _).1 hab
          have hcy : P.LT _ e.2 := (h _ _).1 (.single hbc)
          exact hcover.2 hac hcy
    · intro e he
      rw [mem_comparableEdges]
      exact (h _ _).1 (.single he)
  · rintro ⟨hcover, hcomp⟩ x y
    constructor
    · intro hreach
      induction hreach with
      | single hxy => exact mem_comparableEdges.mp (hcomp hxy)
      | tail _ hyz ih =>
          exact P.lt_trans ih (mem_comparableEdges.mp (hcomp hyz))
    · intro hxy
      have hchain := (lt_iff_transGen_covers P).1 hxy
      exact hchain.mono fun a b hab => hcover (mem_coverEdges.mpr hab)

/-- The reachability fiber of P, represented directly by its edge sets. -/
def ReachabilityFiber {n : ℕ} (P : FinitePoset n) :=
  {E : EdgeSet n // Realizes P E}

/-- Optional non-cover comparisons that may independently be selected. -/
def OptionalChoice {n : ℕ} (P : FinitePoset n) :=
  {A : EdgeSet n // A ∈ (optionalEdges P).powerset}

noncomputable def choicesEquivFiber {n : ℕ} (P : FinitePoset n) :
    OptionalChoice P ≃ ReachabilityFiber P where
  toFun A := by
    refine ⟨coverEdges P ∪ A.1, ?_⟩
    rw [realizes_iff_cover_subset_edges_subset_comparable]
    constructor
    · exact Finset.subset_union_left
    · apply Finset.union_subset (coverEdges_subset_comparableEdges P)
      exact (Finset.mem_powerset.mp A.2).trans Finset.sdiff_subset
  invFun E := by
    refine ⟨E.1 \ coverEdges P, ?_⟩
    rw [Finset.mem_powerset]
    intro e he
    have hsandwich :=
      (realizes_iff_cover_subset_edges_subset_comparable P E.1).1 E.2
    rw [mem_optionalEdges]
    exact ⟨mem_comparableEdges.mp (hsandwich.2 (Finset.mem_sdiff.mp he).1),
      fun hc => (Finset.mem_sdiff.mp he).2 (mem_coverEdges.mpr hc)⟩
  left_inv A := by
    apply Subtype.ext
    ext e
    have hAoptional := Finset.mem_powerset.mp A.2
    constructor
    · intro he
      exact (Finset.mem_union.mp (Finset.mem_sdiff.mp he).1).resolve_left
        (Finset.mem_sdiff.mp he).2
    · intro he
      have heA : e ∉ coverEdges P := by
        intro hecover
        have := hAoptional (show e ∈ A.1 from he)
        exact (mem_optionalEdges.mp this).2 (mem_coverEdges.mp hecover)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ he, heA⟩
  right_inv E := by
    apply Subtype.ext
    ext e
    have hsandwich :=
      (realizes_iff_cover_subset_edges_subset_comparable P E.1).1 E.2
    constructor
    · intro he
      rcases Finset.mem_union.mp he with hecover | hediff
      · exact hsandwich.1 hecover
      · exact (Finset.mem_sdiff.mp hediff).1
    · intro he
      by_cases hecover : e ∈ coverEdges P
      · exact Finset.mem_union_left _ hecover
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, hecover⟩)

noncomputable instance {n : ℕ} (P : FinitePoset n) :
    Fintype (ReachabilityFiber P) := by
  letI : Finite (ReachabilityFiber P) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def optionalChoiceEquivCoe {n : ℕ} (P : FinitePoset n) :
    OptionalChoice P ≃ ↥((optionalEdges P).powerset) where
  toFun A := ⟨A.1, A.2⟩
  invFun A := ⟨A.1, A.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance {n : ℕ} (P : FinitePoset n) :
    Fintype (OptionalChoice P) := by
  letI : Finite (OptionalChoice P) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Paper Theorem 4.2(1): the exact size of a reachability fiber. -/
theorem card_reachabilityFiber {n : ℕ} (P : FinitePoset n) :
    Fintype.card (ReachabilityFiber P) =
      2 ^ ((comparableEdges P).card - (coverEdges P).card) := by
  classical
  calc
    Fintype.card (ReachabilityFiber P) = Fintype.card (OptionalChoice P) :=
      Fintype.card_congr (choicesEquivFiber P).symm
    _ = Fintype.card ↥((optionalEdges P).powerset) :=
      Fintype.card_congr (optionalChoiceEquivCoe P)
    _ = (optionalEdges P).powerset.card := Fintype.card_coe _
    _ = 2 ^ (optionalEdges P).card := Finset.card_powerset _
    _ = 2 ^ ((comparableEdges P).card - (coverEdges P).card) := by
      unfold optionalEdges
      rw [Finset.card_sdiff_of_subset (coverEdges_subset_comparableEdges P)]

/-! ## Skeletons and Markov equivalence -/

def skeleton {n : ℕ} (E : EdgeSet n) : Finset (Sym2 (Fin n)) :=
  E.image fun e => s(e.1, e.2)

theorem mem_skeleton_iff {n : ℕ} {E : EdgeSet n} {x y : Fin n} :
    s(x, y) ∈ skeleton E ↔ (x, y) ∈ E ∨ (y, x) ∈ E := by
  classical
  constructor
  · intro h
    rw [skeleton, Finset.mem_image] at h
    obtain ⟨⟨u, v⟩, huv, hsym⟩ := h
    rcases Sym2.eq_iff.mp hsym with hsame | hswap
    · obtain ⟨rfl, rfl⟩ := hsame
      exact Or.inl huv
    · obtain ⟨rfl, rfl⟩ := hswap
      exact Or.inr huv
  · rintro (hxy | hyx)
    · rw [skeleton, Finset.mem_image]
      exact ⟨(x, y), hxy, rfl⟩
    · rw [skeleton, Finset.mem_image]
      exact ⟨(y, x), hyx, Sym2.eq_swap⟩

/-- Edges respecting one partial order are determined by their undirected
skeleton, because the partial order fixes every allowed orientation. -/
theorem eq_of_skeleton_eq_of_subset_comparable {n : ℕ}
    (P : FinitePoset n) {E F : EdgeSet n}
    (hE : E ⊆ comparableEdges P) (hF : F ⊆ comparableEdges P)
    (hskel : skeleton E = skeleton F) : E = F := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨x, y⟩ := e
    have hs : s(x, y) ∈ skeleton F := by
      rw [← hskel, mem_skeleton_iff]
      exact Or.inl he
    rcases mem_skeleton_iff.mp hs with hxy | hyx
    · exact hxy
    · have hpForward := mem_comparableEdges.mp (hE he)
      have hpBackward := mem_comparableEdges.mp (hF hyx)
      exact False.elim <| hpForward.2
        (P.le_antisymm hpForward.1 hpBackward.1)
  · intro e he
    obtain ⟨x, y⟩ := e
    have hs : s(x, y) ∈ skeleton E := by
      rw [hskel, mem_skeleton_iff]
      exact Or.inl he
    rcases mem_skeleton_iff.mp hs with hxy | hyx
    · exact hxy
    · have hpForward := mem_comparableEdges.mp (hF he)
      have hpBackward := mem_comparableEdges.mp (hE hyx)
      exact False.elim <| hpForward.2
        (P.le_antisymm hpForward.1 hpBackward.1)

/-- An unshielded collider x → z ← y. -/
def IsUnshieldedCollider {n : ℕ} (E : EdgeSet n)
    (x z y : Fin n) : Prop :=
  (x, z) ∈ E ∧ (y, z) ∈ E ∧ x ≠ y ∧ s(x, y) ∉ skeleton E

/-- The standard skeleton-and-unshielded-collider characterization of Markov
equivalence, used here as the finite definition. -/
def MarkovEquivalent {n : ℕ} (E F : EdgeSet n) : Prop :=
  skeleton E = skeleton F ∧
    ∀ x z y, IsUnshieldedCollider E x z y ↔
      IsUnshieldedCollider F x z y

theorem not_markovEquivalent_of_skeleton_ne {n : ℕ} {E F : EdgeSet n}
    (h : skeleton E ≠ skeleton F) : ¬ MarkovEquivalent E F :=
  fun hME => h hME.1

theorem skeleton_injective_on_reachabilityFiber {n : ℕ}
    (P : FinitePoset n) :
    Function.Injective (fun E : ReachabilityFiber P => skeleton E.1) := by
  intro E F hskel
  apply Subtype.ext
  apply eq_of_skeleton_eq_of_subset_comparable P
  · exact ((realizes_iff_cover_subset_edges_subset_comparable P E.1).1 E.2).2
  · exact ((realizes_iff_cover_subset_edges_subset_comparable P F.1).1 F.2).2
  · exact hskel

/-- Paper Theorem 4.2(2): distinct DAGs in one reachability fiber cannot be
Markov equivalent because their skeletons differ. -/
theorem fiber_pairwise_not_markovEquivalent {n : ℕ} (P : FinitePoset n)
    {E F : ReachabilityFiber P} (hne : E ≠ F) :
    ¬ MarkovEquivalent E.1 F.1 := by
  apply not_markovEquivalent_of_skeleton_ne
  intro hskel
  exact hne (skeleton_injective_on_reachabilityFiber P hskel)

/-! ## DAG reachability posets and signatures -/

/-- A finite DAG is an acyclic finite directed edge set. -/
def DAG (n : ℕ) :=
  {E : EdgeSet n // ∀ x : Fin n, ¬ Reach E x x}

namespace DAG

def edges {n : ℕ} (G : DAG n) : EdgeSet n := G.1

@[ext] theorem ext {n : ℕ} {G H : DAG n} (h : G.edges = H.edges) : G = H :=
  Subtype.ext h

end DAG

/-- The reflexive closure of DAG reachability is a partial order. -/
def reachabilityPoset {n : ℕ} (G : DAG n) : FinitePoset n where
  le := fun x y => x = y ∨ Reach G.1 x y
  le_refl := fun x => Or.inl rfl
  le_trans := by
    intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    · exact Or.inr (hxy.trans hyz)
  le_antisymm := by
    intro x y hxy hyx
    rcases hxy with rfl | hxy
    · rfl
    rcases hyx with rfl | hyx
    · rfl
    · exact False.elim (G.2 x (hxy.trans hyx))

@[simp] theorem reachabilityPoset_lt {n : ℕ} (G : DAG n) (x y : Fin n) :
    (reachabilityPoset G).LT x y ↔ Reach G.1 x y := by
  constructor
  · rintro ⟨hxy, hne⟩
    exact hxy.resolve_left hne
  · intro hreach
    refine ⟨Or.inr hreach, ?_⟩
    intro hxy
    subst y
    exact G.2 x hreach

def dagSignatureSet {n : ℕ} (G : DAG n) : Set (PathSignature n) :=
  fullSignatures (reachabilityPoset G)

noncomputable def ReachabilityFiber.toDAG {n : ℕ} {P : FinitePoset n}
    (E : ReachabilityFiber P) : DAG n :=
  ⟨E.1, acyclic_of_realizes E.2⟩

theorem reachabilityPoset_fiber_toDAG {n : ℕ} {P : FinitePoset n}
    (E : ReachabilityFiber P) :
    reachabilityPoset E.toDAG = P := by
  ext x y
  constructor
  · rintro (rfl | hreach)
    · exact P.le_refl x
    · exact ((E.2 x y).1 hreach).1
  · intro hxy
    by_cases hEq : x = y
    · exact Or.inl hEq
    · exact Or.inr ((E.2 x y).2 ⟨hxy, hEq⟩)

/-- Paper Theorem 4.2(3): every DAG in the reachability fiber has the same
full path-signature set. -/
theorem fiber_signature_set_eq {n : ℕ} {P : FinitePoset n}
    (E : ReachabilityFiber P) :
    dagSignatureSet E.toDAG = fullSignatures P := by
  unfold dagSignatureSet
  rw [reachabilityPoset_fiber_toDAG]

/-- Paper Corollary 3.3, DAG recovery from full signatures. -/
theorem dag_recovery_from_path_signatures {n : ℕ} (G H : DAG n)
    (htwo : AtLeastTwoComparablePairs (reachabilityPoset G)) :
    dagSignatureSet G = dagSignatureSet H ↔
      reachabilityPoset H = reachabilityPoset G ∨
      reachabilityPoset H = (reachabilityPoset G).dual := by
  exact recovery_from_path_signatures htwo

/-! ## The complete signature-equivalence fiber -/

def SignatureFiber {n : ℕ} (P : FinitePoset n) :=
  {G : DAG n // dagSignatureSet G = fullSignatures P}

theorem realizes_reachabilityPoset {n : ℕ} (G : DAG n) :
    Realizes (reachabilityPoset G) G.edges := by
  intro x y
  exact (reachabilityPoset_lt G x y).symm

theorem poset_ne_dual_of_atLeastTwo {n : ℕ} {P : FinitePoset n}
    (htwo : AtLeastTwoComparablePairs P) : P ≠ P.dual := by
  rintro hEq
  obtain ⟨e, f, hef, he, hf⟩ := htwo
  rcases he with hxy | hyx
  · have hback : P.LE e.right e.left := by
      exact Eq.mp (congrArg (fun R : FinitePoset n =>
        R.LE e.left e.right) hEq) hxy.1
    exact hxy.2 (P.le_antisymm hxy.1 hback)
  · have hforward : P.LE e.left e.right := by
      exact Eq.mp (congrArg (fun R : FinitePoset n =>
        R.LE e.right e.left) hEq) hyx.1
    exact hyx.2 (P.le_antisymm hyx.1 hforward)

noncomputable def signatureFiberToSum {n : ℕ} {P : FinitePoset n}
    (htwo : AtLeastTwoComparablePairs P) (G : SignatureFiber P) :
    ReachabilityFiber P ⊕ ReachabilityFiber P.dual := by
  have hsig : fullSignatures P =
      fullSignatures (reachabilityPoset G.1) := by
    exact G.2.symm
  have hrecover := (recovery_from_path_signatures htwo).1 hsig
  by_cases hsame : reachabilityPoset G.1 = P
  · exact Sum.inl ⟨G.1.edges, by
      simpa only [hsame] using realizes_reachabilityPoset G.1⟩
  · have hdual : reachabilityPoset G.1 = P.dual :=
      hrecover.resolve_left hsame
    exact Sum.inr ⟨G.1.edges, by
      simpa only [hdual] using realizes_reachabilityPoset G.1⟩

noncomputable def sumToSignatureFiber {n : ℕ} {P : FinitePoset n} :
    ReachabilityFiber P ⊕ ReachabilityFiber P.dual → SignatureFiber P
  | Sum.inl E => ⟨E.toDAG, fiber_signature_set_eq E⟩
  | Sum.inr E => ⟨E.toDAG,
      (fiber_signature_set_eq E).trans (fullSignatures_dual P)⟩

theorem signatureFiberToSum_edges {n : ℕ} {P : FinitePoset n}
    (htwo : AtLeastTwoComparablePairs P) (G : SignatureFiber P) :
    Sum.elim (fun E : ReachabilityFiber P => E.1)
        (fun E : ReachabilityFiber P.dual => E.1)
        (signatureFiberToSum htwo G) = G.1.edges := by
  unfold signatureFiberToSum
  split <;> rfl

noncomputable def signatureFiberEquivSum {n : ℕ} (P : FinitePoset n)
    (htwo : AtLeastTwoComparablePairs P) :
    SignatureFiber P ≃ ReachabilityFiber P ⊕ ReachabilityFiber P.dual where
  toFun := signatureFiberToSum htwo
  invFun := sumToSignatureFiber
  left_inv G := by
    apply Subtype.ext
    apply DAG.ext
    have hedge := signatureFiberToSum_edges htwo G
    generalize hS : signatureFiberToSum htwo G = S at hedge ⊢
    rcases S with E | E
    · change E.1 = G.1.edges
      exact hedge
    · change E.1 = G.1.edges
      exact hedge
  right_inv S := by
    rcases S with E | E
    · unfold signatureFiberToSum sumToSignatureFiber
      dsimp only
      rw [dif_pos (reachabilityPoset_fiber_toDAG E)]
      congr 1
    · have hdualNe : P.dual ≠ P := (poset_ne_dual_of_atLeastTwo htwo).symm
      change signatureFiberToSum htwo
        (sumToSignatureFiber (Sum.inr E)) = Sum.inr E
      unfold signatureFiberToSum sumToSignatureFiber
      dsimp only
      rw [dif_neg (by
        simpa only [reachabilityPoset_fiber_toDAG] using hdualNe)]
      congr 1

noncomputable instance {n : ℕ} : Fintype (DAG n) := by
  letI : Finite (DAG n) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance {n : ℕ} (P : FinitePoset n) :
    Fintype (SignatureFiber P) := by
  letI : Finite (SignatureFiber P) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def reverseEdges {n : ℕ} (E : EdgeSet n) : EdgeSet n :=
  E.image Prod.swap

@[simp] theorem mem_reverseEdges {n : ℕ} {E : EdgeSet n} {x y : Fin n} :
    (x, y) ∈ reverseEdges E ↔ (y, x) ∈ E := by
  simp [reverseEdges, Prod.swap]

@[simp] theorem reverseEdges_reverseEdges {n : ℕ} (E : EdgeSet n) :
    reverseEdges (reverseEdges E) = E := by
  ext e
  obtain ⟨x, y⟩ := e
  simp

theorem reach_reverseEdges {n : ℕ} (E : EdgeSet n) (x y : Fin n) :
    Reach (reverseEdges E) x y ↔ Reach E y x := by
  constructor
  · intro h
    exact h.swap.mono fun a b hab => mem_reverseEdges.mp hab
  · intro h
    exact h.swap.mono fun a b hab => mem_reverseEdges.mpr hab

theorem realizes_reverseEdges {n : ℕ} {P : FinitePoset n} {E : EdgeSet n}
    (h : Realizes P E) : Realizes P.dual (reverseEdges E) := by
  intro x y
  rw [reach_reverseEdges, h, FinitePoset.dual_lt]

noncomputable def reachabilityFiberDualEquiv {n : ℕ} (P : FinitePoset n) :
    ReachabilityFiber P ≃ ReachabilityFiber P.dual where
  toFun E := ⟨reverseEdges E.1, realizes_reverseEdges E.2⟩
  invFun E := ⟨reverseEdges E.1, by
    simpa only [FinitePoset.dual_dual] using realizes_reverseEdges E.2⟩
  left_inv E := by
    apply Subtype.ext
    exact reverseEdges_reverseEdges E.1
  right_inv E := by
    apply Subtype.ext
    exact reverseEdges_reverseEdges E.1

/-- The final cardinality clause of paper Theorem 4.2: in the nonexceptional
case the full signature-equivalence fiber is the disjoint union of the two
reachability fibers and has twice the size of either one. -/
theorem card_signatureFiber {n : ℕ} (P : FinitePoset n)
    (htwo : AtLeastTwoComparablePairs P) :
    Fintype.card (SignatureFiber P) =
      2 ^ (1 + ((comparableEdges P).card - (coverEdges P).card)) := by
  classical
  calc
    Fintype.card (SignatureFiber P) =
        Fintype.card (ReachabilityFiber P ⊕ ReachabilityFiber P.dual) :=
      Fintype.card_congr (signatureFiberEquivSum P htwo)
    _ = Fintype.card (ReachabilityFiber P) +
        Fintype.card (ReachabilityFiber P.dual) := Fintype.card_sum
    _ = Fintype.card (ReachabilityFiber P) +
        Fintype.card (ReachabilityFiber P) := by
      rw [Fintype.card_congr (reachabilityFiberDualEquiv P).symm]
    _ = 2 ^ ((comparableEdges P).card - (coverEdges P).card) +
        2 ^ ((comparableEdges P).card - (coverEdges P).card) := by
      rw [card_reachabilityFiber]
    _ = 2 ^ (1 + ((comparableEdges P).card - (coverEdges P).card)) := by
      rw [Nat.add_comm 1, pow_succ]
      omega

end PathLocalDAG
