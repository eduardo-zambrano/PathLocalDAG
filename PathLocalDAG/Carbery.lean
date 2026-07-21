import PathLocalDAG.Fibers
import DagTesting.MIEquivCollapse

/-!
# Carbery functionals as path-signature observables

The paper's Carbery expression reads two boundary marginals and the
consecutive bivariate marginals along an unoriented path.  Symmetry
`p_{uv}(a,b) = p_{vu}(b,a)` makes that expression a function of the path
signature rather than of an oriented ordering.  `CarberyFormula` records
that fact at exactly the abstraction level used by Proposition 6.1.

The final theorem in this file also connects to the earlier finite-state
implementation: its fixed-permutation DAG blindness was already proved for
the concrete `dagCarberyFunctional`.
-/

namespace PathLocalDAG

/-- A Carbery-type population formula after its boundary and symmetric
bivariate inputs have been assembled by an unoriented path signature. -/
structure CarberyFormula (n : ℕ) (Law Value : Type*) where
  eval : Law → PathSignature n → Value

/-- Evaluate the signature-indexed Carbery formula at an oriented order. -/
def CarberyFormula.atOrder {n : ℕ} {Law Value : Type*}
    (Q : CarberyFormula n Law Value) (p : Law) (L : VertexOrder n) : Value :=
  Q.eval p (signature L)

@[simp] theorem CarberyFormula.atOrder_reverse {n : ℕ}
    {Law Value : Type*} (Q : CarberyFormula n Law Value)
    (p : Law) (L : VertexOrder n) :
    Q.atOrder p L.reverse = Q.atOrder p L := by
  simp [CarberyFormula.atOrder]

def CarberyFormula.toPathLocalFunctional {n : ℕ} {Law Value : Type*}
    (Q : CarberyFormula n Law Value) (p : Law) :
    PathLocalFunctional n Value where
  toFun := Q.atOrder p
  reverse_invariant := Q.atOrder_reverse p

/-- Paper Proposition 6.1, ordering-level statement: Carbery functionals
inherit path-signature blindness. -/
theorem carbery_signature_blindness {n : ℕ} {Law Value : Type*}
    (Q : CarberyFormula n Law Value) (p : Law) {L M : VertexOrder n}
    (h : signature L = signature M) :
    Q.atOrder p L = Q.atOrder p M := by
  exact signature_measurability (Q.toPathLocalFunctional p) h

/-- Paper Proposition 6.1, graph-level consequence for any aggregation that
uses a DAG only through its full signature set. -/
theorem carbery_full_signature_blindness {n : ℕ} {α : Type*}
    (aggregate : Set (PathSignature n) → α) {G H : DAG n}
    (h : dagSignatureSet G = dagSignatureSet H) :
    aggregate (dagSignatureSet G) = aggregate (dagSignatureSet H) :=
  congrArg aggregate h

/-! ## Bridge to the earlier concrete finite-state implementation -/

namespace FiniteStateBridge

open DagTesting

variable {Ω : Fin 3 → Type*} [∀ i, Fintype (Ω i)]
  [∀ i, DecidableEq (Ω i)]

/-- The concrete finite-state bivariate marginal is symmetric.  This is the
analytic fact that allows its consecutive-pair product to descend to an
unoriented path signature. -/
theorem bivariate_marginal_symmetric (p : JointPMF Ω)
    (i j : Fin 3) (hij : i ≠ j) (s : Ω i) (t : Ω j) :
    p.bivariateAny i j hij s t =
      p.bivariateAny j i hij.symm t s :=
  JointPMF.bivariateAny_comm p i j hij s t

/-- The already checked concrete finite-state Q depends on the DAG only
through the selected ordering permutation. -/
theorem concrete_q_fixed_order_blindness
    (G₁ G₂ : FinDAG 3) (p : JointPMF Ω)
    (π₁ : TopologicalOrdering G₁) (π₂ : TopologicalOrdering G₂)
    (hperm : π₁.perm = π₂.perm) :
    dagCarberyFunctional (by omega) G₁ p π₁ =
      dagCarberyFunctional (by omega) G₂ p π₂ :=
  qn_blind_to_dag_given_perm (by omega) G₁ G₂ p π₁ π₂ hperm

end FiniteStateBridge

end PathLocalDAG
