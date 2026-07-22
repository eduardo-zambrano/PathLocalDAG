# Computational replication

This directory reproduces Table 1 and the two-panel explanatory figure in
*What Path-Local Summaries Can Identify About a Causal DAG*.

## Table 1

Run:

```bash
Rscript table1_enumeration.R
```

The script uses base R only. It exhaustively enumerates every labeled DAG
through five vertices, reconstructs its transitive closure, topological
orderings, path-signature set, and Markov-equivalence class, and checks the
paper's exact reachability-fiber formula. The default run writes:

- `table1.csv`, the machine-readable values in Table 1; and
- `table1_rows.tex`, the exact LaTeX rows imported by the manuscript.

Run `Rscript table1_enumeration.R --full` to additionally write the
per-DAG audit files. Those optional files are substantially larger and are
not needed to reproduce the published table.

The checked run used R 4.5.2 and took 41 seconds on an Apple M2 Pro.

## Figure

Run:

```bash
pdflatex -interaction=nonstopmode -halt-on-error figure_pathlocal.tex
```

This creates `figure_pathlocal.pdf`. The source uses TikZ and depicts the two
three-node witnesses used in Proposition 4.1 and Theorem 4.2.

Both outputs can be generated with `make`.
