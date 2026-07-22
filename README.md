# PathLocalDAG

Lean 4 formalization for Eduardo Zambrano, What Path-Local Summaries Can
Identify About a Causal DAG (2026).

This is the current-paper development. Its combinatorial core is separate
from the historical test-centered modules in `DagTesting`; a narrow bridge
reuses the already checked finite-state Carbery functional.

Targeted paper results:

- Lemma 2.2: `signature_eq_iff_reverse`.
- Theorem 3.1: `recovery_from_path_signatures` and
  `fullSignatures_eq_all_of_atMostOne` (including the exceptional class).
- Lemma 3.2: `chiConstant_iff_comparable`.
- Corollary 3.3: `dag_recovery_from_path_signatures`.
- Proposition 4.1: `signature_and_markov_equivalence_incomparable`.
- Theorem 4.2: `realizes_iff_cover_subset_edges_subset_comparable`,
  `choicesEquivFiber`, `card_reachabilityFiber`,
  `fiber_pairwise_not_markovEquivalent`, `fiber_signature_set_eq`,
  `signatureFiberEquivSum`, and `card_signatureFiber`.
- Proposition 5.2: `signature_measurability` and
  `full_signature_aggregation_eq`.
- Proposition 6.1: `carbery_signature_blindness` and
  `carbery_full_signature_blindness`, with the concrete finite-state bridge
  `FiniteStateBridge.concrete_q_fixed_order_blindness`.

## Design

The paper's vertices are represented by `Fin n`.  A `FinitePoset n` is an
explicit partial-order relation, and a `VertexOrder n` is an explicit total
order.  An unoriented labeled Hamiltonian path is represented by the
reversal class `s(L, L.reverse) : Sym2 (VertexOrder n)`.  Directed graphs are
finite sets of ordered pairs, with reachability given by
`Relation.TransGen`.

The exact fiber theorem is constructive: `choicesEquivFiber` is an explicit
equivalence between subsets of the non-cover comparable pairs and all edge
sets realizing the poset.  No enumeration or bounded-size assumption is
used.

For Proposition 6.1, `CarberyFormula` records the mathematical observation
proved in the paper before the proposition: symmetry of the bivariate
marginals makes the formula a function of an unoriented path signature.  The
bridge module separately imports the earlier concrete finite-state marginal
symmetry and fixed-order DAG-blindness theorems.

## Build

```bash
lake build
```

The development targets Lean 4 / mathlib `v4.24.0` and contains no `sorry`,
`admit`, or project-local axioms.

## Computational replication

The `replication/` directory contains the base-R exhaustive enumeration that
generates Table 1 and the TikZ source for the paper's two-panel explanatory
figure:

```bash
cd replication
make
```

The enumeration and figure are computational audits; none of the general
theorems depends on them.
