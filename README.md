# PathLocalDAG

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21509893.svg)](https://doi.org/10.5281/zenodo.21509893)

Lean 4 formalization for Eduardo Zambrano, *Path signatures of causal DAGs:
ancestral recovery and edge identification* (2026).

The development machine-checks the paper's nine formal results:

- Lemma 2.2: `concreteSignature_eq_iff_reverse`, with
  `concreteSignature_eq_iff_signature_eq` and
  `fullConcreteSignatures_eq_iff_fullSignatures_eq` bridging the paper's
  concrete signature to the reversal-class representation used downstream.
- Theorem 3.1: `recovery_from_path_signatures` and
  `fullSignatures_eq_all_of_atMostOne` (including the exceptional class).
- Lemma 3.2: `chiConstant_iff_comparable`.
- Corollary 3.3: `dag_recovery_from_path_signatures`.
- Proposition 4.1: `signature_and_markov_equivalence_incomparable`.
- Theorem 4.2: `realizes_iff_cover_subset_edges_subset_comparable`,
  `choicesEquivFiber`, `card_reachabilityFiber`,
  `fiber_pairwise_not_markovEquivalent`, and `fiber_signature_set_eq`.
- Corollary 4.3: `partial_identification_of_graph`, with
  `signatureFiberEquivSum` and `card_signatureFiber` giving the explicit
  disjoint-union equivalence and exact identified-set cardinality.
- Proposition 5.2: `signature_measurability` and
  `full_signature_aggregation_eq`.
- Proposition 6.1: `carbery_signature_blindness` and
  `carbery_full_signature_blindness`.

## Design

The paper's vertices are represented by `Fin n`.  A `FinitePoset n` is an
explicit partial-order relation, and a `VertexOrder n` is an explicit total
order. `ConcretePathSignature n` records exactly the paper's two objects: the
endpoint set and the set of unordered consecutive labeled pairs. The theorem
`concreteSignature_eq_iff_reverse` proves directly that this concrete object
determines a nonempty vertex order up to reversal. The bridge theorem then
identifies equality of concrete signatures with equality of the canonical
reversal classes `s(L, L.reverse) : Sym2 (VertexOrder n)` used by the recovery
and fiber modules. Directed graphs are finite sets of ordered pairs, with
reachability given by `Relation.TransGen`.

The exact fiber theorem is constructive: `choicesEquivFiber` is an explicit
equivalence between subsets of the non-cover comparable pairs and all edge
sets realizing the poset.  No enumeration or bounded-size assumption is
used.

For Proposition 6.1, `CarberyFormula` records the mathematical observation
proved in the paper before the proposition: symmetry of the bivariate
marginals makes the formula a function of an unoriented path signature.

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

The enumeration and figure illustrate the general results; none of the
theorems depends on them.

## License

The Lean formalization and computational replication materials are released
under the MIT License. See [`LICENSE`](LICENSE).
