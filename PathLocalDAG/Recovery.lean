import PathLocalDAG.Signatures

/-!
# Sign correlations and recovery up to global duality

This file formalizes the constant-correlation mechanism used by the paper's
recovery theorem.
-/

namespace PathLocalDAG

/-- A canonical representative of an unordered pair of distinct vertices. -/
abbrev VertexPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

namespace VertexPair

def left {n : ℕ} (e : VertexPair n) : Fin n := e.1.1
def right {n : ℕ} (e : VertexPair n) : Fin n := e.1.2

theorem left_ne_right {n : ℕ} (e : VertexPair n) : e.left ≠ e.right :=
  ne_of_lt e.2

@[ext] theorem ext {n : ℕ} {e f : VertexPair n}
    (hleft : e.left = f.left) (hright : e.right = f.right) : e = f := by
  apply Subtype.ext
  exact Prod.ext hleft hright

end VertexPair

/-- The pair is comparable in the poset, in either direction. -/
def ComparablePair {n : ℕ} (P : FinitePoset n) (e : VertexPair n) : Prop :=
  P.LT e.left e.right ∨ P.LT e.right e.left

/-- The sign of a canonical pair in a total order. -/
def PairSign {n : ℕ} (L : VertexOrder n) (e : VertexPair n) : Prop :=
  L.Before e.left e.right

/-- Equality of the two signs; this is the paper's product-valued chi
written without choosing numeric encodings for plus and minus one. -/
def Chi {n : ℕ} (L : VertexOrder n) (e f : VertexPair n) : Prop :=
  PairSign L e ↔ PairSign L f

theorem pairSign_reverse {n : ℕ} (L : VertexOrder n) (e : VertexPair n) :
    PairSign L.reverse e ↔ ¬ PairSign L e := by
  simp only [PairSign, VertexOrder.reverse_before]
  constructor
  · exact L.before_asymm
  · intro h
    exact (L.before_iff_not_le).2 fun hle =>
      h ⟨hle, e.left_ne_right⟩

theorem chi_reverse {n : ℕ} (L : VertexOrder n) (e f : VertexPair n) :
    Chi L.reverse e f ↔ Chi L e f := by
  simp only [Chi, pairSign_reverse]
  tauto

/-- The sign correlation is visible from a path signature. -/
theorem chi_eq_of_signature_eq {n : ℕ} {L M : VertexOrder n}
    {e f : VertexPair n} (h : signature L = signature M) :
    Chi L e f ↔ Chi M e f := by
  rcases (signature_eq_iff_reverse L M).1 h with rfl | rfl
  · rfl
  · exact (chi_reverse L e f).symm

/-- Chi is constant across all linear extensions of P. -/
def ChiConstant {n : ℕ} (P : FinitePoset n) (e f : VertexPair n) : Prop :=
  ∀ ⦃L M : VertexOrder n⦄,
    IsLinearExtension P L → IsLinearExtension P M → (Chi L e f ↔ Chi M e f)

theorem pairSign_of_comparable {n : ℕ} {P : FinitePoset n}
    {L : VertexOrder n} (hL : IsLinearExtension P L) (e : VertexPair n)
    (he : ComparablePair P e) :
    PairSign L e ↔ P.LT e.left e.right := by
  rcases he with hforward | hbackward
  · exact iff_of_true (hL.before_of_lt hforward) hforward
  · have hnotL : ¬ PairSign L e :=
      L.before_asymm (hL.before_of_lt hbackward)
    have hnotP : ¬ P.LT e.left e.right := by
      intro h
      exact h.2 (P.le_antisymm h.1 hbackward.1)
    exact iff_of_false hnotL hnotP

theorem chiConstant_of_comparable {n : ℕ} {P : FinitePoset n}
    {e f : VertexPair n} (he : ComparablePair P e)
    (hf : ComparablePair P f) : ChiConstant P e f := by
  intro L M hL hM
  simp only [Chi, pairSign_of_comparable hL e he,
    pairSign_of_comparable hL f hf, pairSign_of_comparable hM e he,
    pairSign_of_comparable hM f hf]

/-! ## A block-lexicographic total order -/

/-- Refine a finite block number by an existing labeled total order. -/
def blockLexOrder {n : ℕ} (block : Fin n → ℕ) (B : VertexOrder n) :
    VertexOrder n where
  le := fun x y => block x < block y ∨ block x = block y ∧ B.LE x y
  le_refl := fun x => Or.inr ⟨rfl, B.le_refl x⟩
  le_trans := by
    intro x y z hxy hyz
    rcases hxy with hxy | ⟨hxy, hBxy⟩
    · rcases hyz with hyz | ⟨hyz, _⟩
      · exact Or.inl (lt_trans hxy hyz)
      · exact Or.inl (hyz ▸ hxy)
    · rcases hyz with hyz | ⟨hyz, hByz⟩
      · exact Or.inl (hxy ▸ hyz)
      · exact Or.inr ⟨hxy.trans hyz, B.le_trans hBxy hByz⟩
  le_antisymm := by
    intro x y hxy hyx
    rcases hxy with hxy | ⟨hblock, hBxy⟩
    · rcases hyx with hyx | ⟨hyx, _⟩ <;> omega
    · rcases hyx with hyx | ⟨_, hByx⟩
      · omega
      · exact B.le_antisymm hBxy hByx
  le_total := by
    intro x y
    rcases lt_trichotomy (block x) (block y) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases B.le_total x y with hB | hB
      · exact Or.inl (Or.inr ⟨h, hB⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hB⟩)
    · exact Or.inr (Or.inl h)

@[simp] theorem blockLexOrder_le {n : ℕ} (block : Fin n → ℕ)
    (B : VertexOrder n) (x y : Fin n) :
    (blockLexOrder block B).LE x y ↔
      block x < block y ∨ block x = block y ∧ B.LE x y :=
  Iff.rfl

/-! ## Flipping one incomparable pair -/

def Incomparable {n : ℕ} (P : FinitePoset n) (x y : Fin n) : Prop :=
  ¬ P.LT x y ∧ ¬ P.LT y x

def belowEither {n : ℕ} (P : FinitePoset n) (x y z : Fin n) : Prop :=
  P.LT z x ∨ P.LT z y

/-- Four blocks: the common strict down-set, x/y in a chosen order, and
everything else. -/
noncomputable def pairBlock {n : ℕ} (P : FinitePoset n)
    (x y : Fin n) (swap : Bool) (z : Fin n) : ℕ := by
  classical
  exact if belowEither P x y z then 0
    else if z = x then (if swap then 2 else 1)
    else if z = y then (if swap then 1 else 2)
    else 3

theorem not_belowEither_left {n : ℕ} {P : FinitePoset n} {x y : Fin n}
    (hinc : Incomparable P x y) : ¬ belowEither P x y x := by
  rintro (hxx | hxy)
  · exact P.lt_irrefl x hxx
  · exact hinc.1 hxy

theorem not_belowEither_right {n : ℕ} {P : FinitePoset n} {x y : Fin n}
    (hinc : Incomparable P x y) : ¬ belowEither P x y y := by
  rintro (hyx | hyy)
  · exact hinc.2 hyx
  · exact P.lt_irrefl y hyy

@[simp] theorem pairBlock_left {n : ℕ} {P : FinitePoset n} {x y : Fin n}
    (hinc : Incomparable P x y) (swap : Bool) :
    pairBlock P x y swap x = if swap then 2 else 1 := by
  simp [pairBlock, not_belowEither_left hinc]

@[simp] theorem pairBlock_right {n : ℕ} {P : FinitePoset n} {x y : Fin n}
    (hxy : x ≠ y) (hinc : Incomparable P x y) (swap : Bool) :
    pairBlock P x y swap y = if swap then 1 else 2 := by
  simp [pairBlock, not_belowEither_right hinc, hxy.symm]

theorem pairBlock_of_below {n : ℕ} {P : FinitePoset n} {x y z : Fin n}
    (swap : Bool) (hz : belowEither P x y z) :
    pairBlock P x y swap z = 0 := by
  simp [pairBlock, hz]

theorem pairBlock_of_other {n : ℕ} {P : FinitePoset n} {x y z : Fin n}
    (swap : Bool) (hz : ¬ belowEither P x y z) (hzx : z ≠ x) (hzy : z ≠ y) :
    pairBlock P x y swap z = 3 := by
  simp [pairBlock, hz, hzx, hzy]

theorem belowEither_down_closed {n : ℕ} {P : FinitePoset n}
    {x y a b : Fin n} (hab : P.LT a b) (hb : belowEither P x y b) :
    belowEither P x y a := by
  rcases hb with hbx | hby
  · exact Or.inl (P.lt_trans hab hbx)
  · exact Or.inr (P.lt_trans hab hby)

theorem pairBlockOrder_isExtension {n : ℕ} {P : FinitePoset n}
    {x y : Fin n} (hxy : x ≠ y) (hinc : Incomparable P x y)
    (swap : Bool) {B : VertexOrder n} (hB : IsLinearExtension P B) :
    IsLinearExtension P (blockLexOrder (pairBlock P x y swap) B) := by
  intro a b hab
  by_cases hab_eq : a = b
  · subst b
    exact (blockLexOrder (pairBlock P x y swap) B).le_refl a
  have hab_lt : P.LT a b := ⟨hab, hab_eq⟩
  by_cases hbdown : belowEither P x y b
  · have hadown := belowEither_down_closed hab_lt hbdown
    exact Or.inr ⟨by
      rw [pairBlock_of_below swap hadown, pairBlock_of_below swap hbdown], hB hab⟩
  by_cases hbx : b = x
  · subst b
    have hadown : belowEither P x y a := Or.inl hab_lt
    rw [blockLexOrder_le, pairBlock_of_below swap hadown,
      pairBlock_left hinc swap]
    cases swap <;> simp
  by_cases hby : b = y
  · subst b
    have hadown : belowEither P x y a := Or.inr hab_lt
    rw [blockLexOrder_le, pairBlock_of_below swap hadown,
      pairBlock_right hxy hinc swap]
    cases swap <;> simp
  have hbblock : pairBlock P x y swap b = 3 :=
    pairBlock_of_other swap hbdown hbx hby
  by_cases hadown : belowEither P x y a
  · rw [blockLexOrder_le, pairBlock_of_below swap hadown, hbblock]
    simp
  by_cases hax : a = x
  · subst a
    rw [blockLexOrder_le, pairBlock_left hinc swap, hbblock]
    cases swap <;> simp
  by_cases hay : a = y
  · subst a
    rw [blockLexOrder_le, pairBlock_right hxy hinc swap, hbblock]
    cases swap <;> simp
  rw [blockLexOrder_le, pairBlock_of_other swap hadown hax hay, hbblock]
  exact Or.inr ⟨rfl, hB hab⟩

theorem pairBlock_eq_of_other {n : ℕ} {P : FinitePoset n}
    {x y z : Fin n} (hzx : z ≠ x) (hzy : z ≠ y) :
    pairBlock P x y false z = pairBlock P x y true z := by
  by_cases hz : belowEither P x y z
  · rw [pairBlock_of_below false hz, pairBlock_of_below true hz]
  · rw [pairBlock_of_other false hz hzx hzy,
      pairBlock_of_other true hz hzx hzy]

/-- Outside the distinguished unordered pair, swapping its two middle
blocks changes no pairwise comparison. -/
theorem pairBlockOrder_le_iff {n : ℕ} {P : FinitePoset n}
    {x y a b : Fin n} (hxy : x ≠ y) (hinc : Incomparable P x y)
    (hab : a ≠ b)
    (hforward : ¬ (a = x ∧ b = y)) (hbackward : ¬ (a = y ∧ b = x))
    (B : VertexOrder n) :
    (blockLexOrder (pairBlock P x y false) B).LE a b ↔
      (blockLexOrder (pairBlock P x y true) B).LE a b := by
  by_cases hax : a = x
  · subst a
    have hby : b ≠ y := fun h => hforward ⟨rfl, h⟩
    have hbx : b ≠ x := fun h => hab h.symm
    by_cases hbdown : belowEither P x y b
    · rw [blockLexOrder_le, blockLexOrder_le,
        pairBlock_left hinc false, pairBlock_left hinc true,
        pairBlock_of_below false hbdown, pairBlock_of_below true hbdown]
      simp
    · rw [blockLexOrder_le, blockLexOrder_le,
        pairBlock_left hinc false, pairBlock_left hinc true,
        pairBlock_of_other false hbdown hbx hby,
        pairBlock_of_other true hbdown hbx hby]
      simp
  by_cases hay : a = y
  · subst a
    have hbx : b ≠ x := fun h => hbackward ⟨rfl, h⟩
    have hby : b ≠ y := fun h => hab h.symm
    by_cases hbdown : belowEither P x y b
    · rw [blockLexOrder_le, blockLexOrder_le,
        pairBlock_right hxy hinc false, pairBlock_right hxy hinc true,
        pairBlock_of_below false hbdown, pairBlock_of_below true hbdown]
      simp
    · rw [blockLexOrder_le, blockLexOrder_le,
        pairBlock_right hxy hinc false, pairBlock_right hxy hinc true,
        pairBlock_of_other false hbdown hbx hby,
        pairBlock_of_other true hbdown hbx hby]
      simp
  by_cases hbx : b = x
  · subst b
    by_cases hadown : belowEither P x y a
    · rw [blockLexOrder_le, blockLexOrder_le,
        pairBlock_of_below false hadown, pairBlock_of_below true hadown,
        pairBlock_left hinc false, pairBlock_left hinc true]
      simp
    · rw [blockLexOrder_le, blockLexOrder_le,
        pairBlock_of_other false hadown hax hay,
        pairBlock_of_other true hadown hax hay,
        pairBlock_left hinc false, pairBlock_left hinc true]
      simp
  by_cases hby : b = y
  · subst b
    by_cases hadown : belowEither P x y a
    · rw [blockLexOrder_le, blockLexOrder_le,
        pairBlock_of_below false hadown, pairBlock_of_below true hadown,
        pairBlock_right hxy hinc false, pairBlock_right hxy hinc true]
      simp
    · rw [blockLexOrder_le, blockLexOrder_le,
        pairBlock_of_other false hadown hax hay,
        pairBlock_of_other true hadown hax hay,
        pairBlock_right hxy hinc false, pairBlock_right hxy hinc true]
      simp
  rw [blockLexOrder_le, blockLexOrder_le,
    pairBlock_eq_of_other hax hay, pairBlock_eq_of_other hbx hby]

theorem incomparable_of_not_comparable {n : ℕ} {P : FinitePoset n}
    {e : VertexPair n} (he : ¬ ComparablePair P e) :
    Incomparable P e.left e.right := by
  constructor <;> intro h
  · exact he (Or.inl h)
  · exact he (Or.inr h)

theorem forward_pairSign {n : ℕ} {P : FinitePoset n} (e : VertexPair n)
    (hinc : Incomparable P e.left e.right) (B : VertexOrder n) :
    PairSign (blockLexOrder (pairBlock P e.left e.right false) B) e := by
  constructor
  · rw [blockLexOrder_le, pairBlock_left hinc false,
      pairBlock_right e.left_ne_right hinc false]
    simp
  · exact e.left_ne_right

theorem swapped_pairSign_reverse {n : ℕ} {P : FinitePoset n}
    (e : VertexPair n) (hinc : Incomparable P e.left e.right)
    (B : VertexOrder n) :
    (blockLexOrder (pairBlock P e.left e.right true) B).Before
      e.right e.left := by
  constructor
  · rw [blockLexOrder_le, pairBlock_right e.left_ne_right hinc true,
      pairBlock_left hinc true]
    simp
  · exact e.left_ne_right.symm

theorem other_pairSign_unchanged {n : ℕ} {P : FinitePoset n}
    {e f : VertexPair n} (hef : e ≠ f)
    (hinc : Incomparable P e.left e.right) (B : VertexOrder n) :
    PairSign (blockLexOrder (pairBlock P e.left e.right false) B) f ↔
      PairSign (blockLexOrder (pairBlock P e.left e.right true) B) f := by
  apply and_congr
  · apply pairBlockOrder_le_iff e.left_ne_right hinc f.left_ne_right
    · rintro ⟨hl, hr⟩
      apply hef
      exact VertexPair.ext hl.symm hr.symm
    · rintro ⟨hl, hr⟩
      have h₁ := f.2
      have h₂ := e.2
      simp only [VertexPair.left, VertexPair.right] at hl hr h₁ h₂
      omega
  · rfl

/-- If one pair is incomparable, its sign can be flipped while every other
pair's sign stays fixed. -/
theorem not_chiConstant_of_incomparable_left {n : ℕ} {P : FinitePoset n}
    {e f : VertexPair n} (hef : e ≠ f) (he : ¬ ComparablePair P e) :
    ¬ ChiConstant P e f := by
  intro hconstant
  let B := someLinearExtension P
  let L₀ := blockLexOrder (pairBlock P e.left e.right false) B
  let L₁ := blockLexOrder (pairBlock P e.left e.right true) B
  have hinc := incomparable_of_not_comparable he
  have hB : IsLinearExtension P B := someLinearExtension_isExtension P
  have hL₀ : IsLinearExtension P L₀ :=
    pairBlockOrder_isExtension e.left_ne_right hinc false hB
  have hL₁ : IsLinearExtension P L₁ :=
    pairBlockOrder_isExtension e.left_ne_right hinc true hB
  have he₀ : PairSign L₀ e := forward_pairSign e hinc B
  have he₁ : ¬ PairSign L₁ e :=
    L₁.before_asymm (swapped_pairSign_reverse e hinc B)
  have hf : PairSign L₀ f ↔ PairSign L₁ f :=
    other_pairSign_unchanged hef hinc B
  have hc := hconstant hL₀ hL₁
  simp only [Chi] at hc
  tauto

theorem chiConstant_comm {n : ℕ} {P : FinitePoset n}
    {e f : VertexPair n} :
    ChiConstant P e f ↔ ChiConstant P f e := by
  constructor <;> intro h L M hL hM
  · have := h hL hM
    simp only [Chi] at this ⊢
    tauto
  · have := h hL hM
    simp only [Chi] at this ⊢
    tauto

/-- Paper Lemma 3.2: constant correlation occurs exactly for two comparable
pairs. -/
theorem chiConstant_iff_comparable {n : ℕ} {P : FinitePoset n}
    {e f : VertexPair n} (hef : e ≠ f) :
    ChiConstant P e f ↔ ComparablePair P e ∧ ComparablePair P f := by
  constructor
  · intro h
    constructor
    · by_contra he
      exact not_chiConstant_of_incomparable_left hef he h
    · by_contra hf
      exact not_chiConstant_of_incomparable_left hef.symm hf
        ((chiConstant_comm).1 h)
  · rintro ⟨he, hf⟩
    exact chiConstant_of_comparable he hf

/-! ## Recovering the comparable pairs -/

theorem chiConstant_congr_fullSignatures {n : ℕ} {P Q : FinitePoset n}
    (hS : fullSignatures P = fullSignatures Q) (e f : VertexPair n) :
    ChiConstant P e f ↔ ChiConstant Q e f := by
  have forward : ∀ {A B : FinitePoset n},
      fullSignatures A = fullSignatures B →
      ChiConstant A e f → ChiConstant B e f := by
    intro A B hAB h L M hL hM
    obtain ⟨L', hL', hsigL⟩ :=
      (show signature L ∈ fullSignatures A by
        rw [hAB]
        exact signature_mem_fullSignatures hL)
    obtain ⟨M', hM', hsigM⟩ :=
      (show signature M ∈ fullSignatures A by
        rw [hAB]
        exact signature_mem_fullSignatures hM)
    have hc := h hL' hM'
    have hχL := chi_eq_of_signature_eq (e := e) (f := f) hsigL.symm
    have hχM := chi_eq_of_signature_eq (e := e) (f := f) hsigM.symm
    tauto
  constructor
  · exact forward hS
  · exact forward hS.symm

/-- The nondegeneracy hypothesis in Theorem 3.1. -/
def AtLeastTwoComparablePairs {n : ℕ} (P : FinitePoset n) : Prop :=
  ∃ e f : VertexPair n, e ≠ f ∧ ComparablePair P e ∧ ComparablePair P f

theorem comparable_mono_of_fullSignatures_eq {n : ℕ} {P Q : FinitePoset n}
    (hS : fullSignatures P = fullSignatures Q)
    (htwo : AtLeastTwoComparablePairs P) (e : VertexPair n)
    (he : ComparablePair P e) : ComparablePair Q e := by
  obtain ⟨a, b, hab, ha, hb⟩ := htwo
  by_cases hea : e = a
  · have hec : ChiConstant P e b := by
      apply chiConstant_of_comparable he hb
    have hQc := (chiConstant_congr_fullSignatures hS e b).1 hec
    have heb : e ≠ b := by simpa [hea] using hab
    exact ((chiConstant_iff_comparable heb).1 hQc).1
  · have hec : ChiConstant P e a := chiConstant_of_comparable he ha
    have hQc := (chiConstant_congr_fullSignatures hS e a).1 hec
    exact ((chiConstant_iff_comparable hea).1 hQc).1

theorem atLeastTwoComparablePairs_of_fullSignatures_eq {n : ℕ}
    {P Q : FinitePoset n} (hS : fullSignatures P = fullSignatures Q)
    (htwo : AtLeastTwoComparablePairs P) :
    AtLeastTwoComparablePairs Q := by
  have htwoP := htwo
  obtain ⟨a, b, hab, ha, hb⟩ := htwo
  exact ⟨a, b, hab,
    comparable_mono_of_fullSignatures_eq hS htwoP a ha,
    comparable_mono_of_fullSignatures_eq hS htwoP b hb⟩

theorem comparable_iff_of_fullSignatures_eq {n : ℕ}
    {P Q : FinitePoset n} (hS : fullSignatures P = fullSignatures Q)
    (htwo : AtLeastTwoComparablePairs P) (e : VertexPair n) :
    ComparablePair P e ↔ ComparablePair Q e := by
  constructor
  · exact comparable_mono_of_fullSignatures_eq hS htwo e
  · exact comparable_mono_of_fullSignatures_eq hS.symm
      (atLeastTwoComparablePairs_of_fullSignatures_eq hS htwo) e

def ComparableVertices {n : ℕ} (P : FinitePoset n) (x y : Fin n) : Prop :=
  P.LT x y ∨ P.LT y x

theorem comparableVertices_iff_of_pairs {n : ℕ} {P Q : FinitePoset n}
    (hpairs : ∀ e : VertexPair n, ComparablePair P e ↔ ComparablePair Q e)
    {x y : Fin n} (hxy : x ≠ y) :
    ComparableVertices P x y ↔ ComparableVertices Q x y := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · let e : VertexPair n := ⟨(x, y), hlt⟩
    simpa [e, ComparableVertices, ComparablePair, VertexPair.left,
      VertexPair.right] using hpairs e
  · let e : VertexPair n := ⟨(y, x), hgt⟩
    simpa [e, ComparableVertices, ComparablePair, VertexPair.left,
      VertexPair.right, or_comm] using hpairs e

/-- If two posets have the same comparable pairs and share one linear
extension, then all comparison orientations agree. -/
theorem eq_of_same_comparabilities_and_extension {n : ℕ}
    {P Q : FinitePoset n}
    (hcomp : ∀ ⦃x y : Fin n⦄, x ≠ y →
      (ComparableVertices P x y ↔ ComparableVertices Q x y))
    {L : VertexOrder n} (hP : IsLinearExtension P L)
    (hQ : IsLinearExtension Q L) : P = Q := by
  ext x y
  constructor
  · intro hxy
    by_cases heq : x = y
    · subst y
      exact Q.le_refl x
    have hp : P.LT x y := ⟨hxy, heq⟩
    rcases (hcomp heq).1 (Or.inl hp) with hq | hq
    · exact hq.1
    · exact False.elim <|
        L.before_asymm (hP.before_of_lt hp) (hQ.before_of_lt hq)
  · intro hxy
    by_cases heq : x = y
    · subst y
      exact P.le_refl x
    have hq : Q.LT x y := ⟨hxy, heq⟩
    rcases (hcomp heq).2 (Or.inl hq) with hp | hp
    · exact hp.1
    · exact False.elim <|
        L.before_asymm (hQ.before_of_lt hq) (hP.before_of_lt hp)

/-- Paper Theorem 3.1, nondegenerate recovery statement. -/
theorem recovery_from_path_signatures {n : ℕ} {P Q : FinitePoset n}
    (htwo : AtLeastTwoComparablePairs P) :
    fullSignatures P = fullSignatures Q ↔ Q = P ∨ Q = P.dual := by
  constructor
  · intro hS
    let L := someLinearExtension P
    have hL : IsLinearExtension P L := someLinearExtension_isExtension P
    obtain ⟨M, hM, hsig⟩ :=
      (show signature L ∈ fullSignatures Q by
        rw [← hS]
        exact signature_mem_fullSignatures hL)
    have hpairs := comparable_iff_of_fullSignatures_eq hS htwo
    have hcomp : ∀ ⦃x y : Fin n⦄, x ≠ y →
        (ComparableVertices P x y ↔ ComparableVertices Q x y) := by
      intro x y hxy
      exact comparableVertices_iff_of_pairs hpairs hxy
    rcases (signature_eq_iff_reverse L M).1 hsig.symm with hML | hMrev
    · subst M
      exact Or.inl (eq_of_same_comparabilities_and_extension hcomp hL hM).symm
    · subst M
      have hQdual : IsLinearExtension Q.dual L := by
        intro x y hxy
        exact hM (x := y) (y := x) hxy
      have hcompDual : ∀ ⦃x y : Fin n⦄, x ≠ y →
          (ComparableVertices P x y ↔ ComparableVertices Q.dual x y) := by
        intro x y hxy
        simpa only [ComparableVertices, FinitePoset.dual_lt, or_comm]
          using hcomp hxy
      have hPQdual :=
        eq_of_same_comparabilities_and_extension hcompDual hL hQdual
      exact Or.inr <| by
        have hdual := congrArg FinitePoset.dual hPQdual
        simpa only [FinitePoset.dual_dual] using hdual.symm
  · rintro (rfl | rfl)
    · rfl
    · exact (fullSignatures_dual P).symm

/-! ## The exceptional signature class -/

/-- A poset has at most one comparable unordered pair exactly when it has at
most one strict directed comparison. Antisymmetry makes the directed version
equivalent to the paper's unordered formulation. -/
def AtMostOneComparablePair {n : ℕ} (P : FinitePoset n) : Prop :=
  ∀ ⦃x y u v : Fin n⦄, P.LT x y → P.LT u v → x = u ∧ y = v

/-- Every abstract path signature that is represented by a total order. -/
def allPathSignatures (n : ℕ) : Set (PathSignature n) :=
  Set.range signature

theorem extension_or_reverse_of_atMostOne {n : ℕ} {P : FinitePoset n}
    (hone : AtMostOneComparablePair P) (L : VertexOrder n) :
    IsLinearExtension P L ∨ IsLinearExtension P L.reverse := by
  by_cases hex : ∃ x y, P.LT x y
  · obtain ⟨a, b, hab⟩ := hex
    rcases L.le_total a b with hLab | hLba
    · left
      intro x y hxy
      by_cases hEq : x = y
      · subst y
        exact L.le_refl x
      · have hlt : P.LT x y := ⟨hxy, hEq⟩
        obtain ⟨rfl, rfl⟩ := hone hlt hab
        exact hLab
    · right
      intro x y hxy
      by_cases hEq : x = y
      · subst y
        exact L.le_refl x
      · have hlt : P.LT x y := ⟨hxy, hEq⟩
        obtain ⟨rfl, rfl⟩ := hone hlt hab
        exact hLba
  · left
    intro x y hxy
    by_cases hEq : x = y
    · subst y
      exact L.le_refl x
    · exact False.elim <| hex ⟨x, y, hxy, hEq⟩

/-- The exceptional clause of paper Theorem 3.1: an antichain and every
poset with exactly one comparable pair have the maximal signature set. -/
theorem fullSignatures_eq_all_of_atMostOne {n : ℕ} {P : FinitePoset n}
    (hone : AtMostOneComparablePair P) :
    fullSignatures P = allPathSignatures n := by
  ext τ
  constructor
  · rintro ⟨L, hL, rfl⟩
    exact ⟨L, rfl⟩
  · rintro ⟨L, rfl⟩
    rcases extension_or_reverse_of_atMostOne hone L with hL | hLrev
    · exact signature_mem_fullSignatures hL
    · simpa using (signature_mem_fullSignatures hLrev)

end PathLocalDAG
