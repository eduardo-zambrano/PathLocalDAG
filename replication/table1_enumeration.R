#!/usr/bin/env Rscript

# Exhaustive falsification exercise for ordering-signature equivalence.
#
# For a labeled DAG G, let L(G) be its topological orderings.  The Carbery
# ordering signature of an ordering is its pair of boundary vertices and its
# consecutive unordered vertex pairs.  Because an ordering is a Hamiltonian
# path, this is equivalently the ordering modulo global reversal.
#
# This script enumerates every labeled DAG through n = 5 and compares:
#   * equality of the full signature sets induced by L(G),
#   * equality under a deterministic lexicographically-first ordering rule,
#   * Markov equivalence (same skeleton and unshielded colliders), and
#   * equality of transitive closures up to global edge reversal.
# For every enumerated reachability poset P, it also verifies the exact fiber
# characterization Cov(P) subset E subset Comp(P) and the corresponding
# cardinality 2^(|Comp(P)| - |Cov(P)|).
#
# It uses base R only.  Generated CSV files are written beside this script.

script_arg <- grep("^--file=", commandArgs(), value = TRUE)
script_path <- if (length(script_arg)) {
  normalizePath(sub("^--file=", "", script_arg[[1]]))
} else {
  normalizePath("replication/table1_enumeration.R")
}
output_dir <- dirname(script_path)
write_full_audit <- "--full" %in% commandArgs(trailingOnly = TRUE)

permutations <- function(values) {
  values <- as.integer(values)
  if (length(values) == 1L) return(matrix(values, nrow = 1L))
  out <- lapply(seq_along(values), function(i) {
    rest <- permutations(values[-i])
    cbind(values[[i]], rest)
  })
  do.call(rbind, out)
}

canonical_path <- function(ordering) {
  forward <- paste(ordering, collapse = "-")
  backward <- paste(rev(ordering), collapse = "-")
  min(forward, backward)
}

decode_ternary <- function(code, m) {
  states <- integer(m)
  for (k in seq_len(m)) {
    states[[k]] <- code %% 3L
    code <- code %/% 3L
  }
  states
}

adjacency_from_states <- function(states, pairs, n) {
  adj <- matrix(FALSE, n, n)
  for (k in seq_along(states)) {
    if (states[[k]] == 1L) adj[pairs[k, 1L], pairs[k, 2L]] <- TRUE
    if (states[[k]] == 2L) adj[pairs[k, 2L], pairs[k, 1L]] <- TRUE
  }
  adj
}

edge_key <- function(adj) {
  edges <- which(adj, arr.ind = TRUE)
  if (!nrow(edges)) return("empty")
  edges <- edges[order(edges[, 1L], edges[, 2L]), , drop = FALSE]
  paste(sprintf("%d>%d", edges[, 1L], edges[, 2L]), collapse = ",")
}

transitive_closure <- function(adj) {
  reach <- adj
  n <- nrow(adj)
  for (k in seq_len(n)) {
    for (i in seq_len(n)) {
      if (reach[i, k]) reach[i, ] <- reach[i, ] | reach[k, ]
    }
  }
  diag(reach) <- FALSE
  reach
}

adjacency_from_edge_key <- function(key, n) {
  adj <- matrix(FALSE, n, n)
  if (identical(key, "empty")) return(adj)
  edges <- strsplit(key, ",", fixed = TRUE)[[1L]]
  for (edge in edges) {
    vertices <- as.integer(strsplit(edge, ">", fixed = TRUE)[[1L]])
    adj[vertices[[1L]], vertices[[2L]]] <- TRUE
  }
  adj
}

cover_relations <- function(reach) {
  cover <- reach
  n <- nrow(reach)
  for (i in seq_len(n)) {
    for (j in seq_len(n)) {
      if (!reach[i, j]) next
      intermediates <- reach[i, ] & reach[, j]
      cover[i, j] <- !any(intermediates)
    }
  }
  cover
}

# Exact finite audit of the reachability-fiber theorem.  For a closure P,
# every realizing DAG must contain all cover relations and may independently
# choose every other comparable pair.
audit_reachability_fibers <- function(df) {
  n <- unique(df$n)
  stopifnot(length(n) == 1L)
  closure_groups <- split(df, df$closure_key)
  fiber_size_failures <- 0L
  edge_interval_failures <- 0L

  for (g in closure_groups) {
    reach <- adjacency_from_edge_key(g$closure_key[[1L]], n)
    cover <- cover_relations(reach)
    expected_size <- 2 ^ (sum(reach) - sum(cover))
    if (nrow(g) != expected_size) {
      fiber_size_failures <- fiber_size_failures + 1L
    }

    for (key in g$graph_key) {
      adj <- adjacency_from_edge_key(key, n)
      contains_covers <- all(!cover | adj)
      uses_only_comparabilities <- all(!adj | reach)
      if (!contains_covers || !uses_only_comparabilities) {
        edge_interval_failures <- edge_interval_failures + 1L
      }
    }
  }

  data.frame(
    n_reachability_fibers = length(closure_groups),
    reachability_fiber_size_failures = fiber_size_failures,
    reachability_edge_interval_failures = edge_interval_failures
  )
}

is_weakly_connected <- function(adj) {
  n <- nrow(adj)
  if (n <= 1L) return(TRUE)
  skeleton <- adj | t(adj)
  seen <- rep(FALSE, n)
  frontier <- 1L
  seen[[1L]] <- TRUE
  while (length(frontier)) {
    neighbors <- which(colSums(skeleton[frontier, , drop = FALSE]) > 0L)
    new_vertices <- neighbors[!seen[neighbors]]
    if (!length(new_vertices)) break
    seen[new_vertices] <- TRUE
    frontier <- new_vertices
  }
  all(seen)
}

markov_key <- function(adj) {
  n <- nrow(adj)
  skeleton <- adj | t(adj)
  diag(skeleton) <- FALSE
  skeleton_pairs <- character(0)
  for (i in seq_len(n - 1L)) {
    for (j in (i + 1L):n) {
      if (skeleton[i, j]) {
        skeleton_pairs <- c(skeleton_pairs, sprintf("%d-%d", i, j))
      }
    }
  }

  colliders <- character(0)
  for (child in seq_len(n)) {
    parents <- which(adj[, child])
    if (length(parents) < 2L) next
    parent_pairs <- combn(parents, 2L)
    for (k in seq_len(ncol(parent_pairs))) {
      a <- parent_pairs[1L, k]
      b <- parent_pairs[2L, k]
      if (!skeleton[a, b]) {
        colliders <- c(colliders, sprintf("%d>%d<%d", a, child, b))
      }
    }
  }
  paste0(
    "S[", paste(sort(skeleton_pairs), collapse = ";"), "]",
    "V[", paste(sort(colliders), collapse = ";"), "]"
  )
}

pair_total <- function(counts) sum(counts * (counts - 1) / 2)

pairs_equal_first_not_second <- function(df, first, second) {
  first_groups <- split(df, df[[first]])
  sum(vapply(first_groups, function(g) {
    pair_total(nrow(g)) - pair_total(table(g[[second]]))
  }, numeric(1)))
}

enumerate_dags <- function(n) {
  cat(sprintf("Enumerating n=%d ...\n", n))
  perms <- permutations(seq_len(n))
  perm_strings <- apply(perms, 1L, paste, collapse = "-")
  ord <- order(perm_strings)
  perms <- perms[ord, , drop = FALSE]
  signature_by_perm <- apply(perms, 1L, canonical_path)

  positions <- matrix(0L, nrow(perms), n)
  for (row in seq_len(nrow(perms))) {
    positions[row, perms[row, ]] <- seq_len(n)
  }

  pairs <- t(combn(seq_len(n), 2L))
  n_candidates <- 3L ^ nrow(pairs)
  records <- vector("list", n_candidates)
  kept <- 0L

  for (code in 0:(n_candidates - 1L)) {
    states <- decode_ternary(code, nrow(pairs))
    valid <- rep(TRUE, nrow(perms))
    for (k in seq_along(states)) {
      if (states[[k]] == 1L) {
        valid <- valid & positions[, pairs[k, 1L]] < positions[, pairs[k, 2L]]
      } else if (states[[k]] == 2L) {
        valid <- valid & positions[, pairs[k, 2L]] < positions[, pairs[k, 1L]]
      }
      if (!any(valid)) break
    }
    if (!any(valid)) next

    adj <- adjacency_from_states(states, pairs, n)
    topo_idx <- which(valid)
    signatures <- sort(unique(signature_by_perm[topo_idx]))
    closure <- transitive_closure(adj)
    closure_key <- edge_key(closure)
    dual_key <- edge_key(t(closure))

    reverse_states <- states
    reverse_states[states == 1L] <- 2L
    reverse_states[states == 2L] <- 1L

    kept <- kept + 1L
    records[[kept]] <- data.frame(
      n = n,
      graph_code = code,
      graph_key = edge_key(adj),
      reverse_graph_code = sum(reverse_states * 3L ^ (seq_along(states) - 1L)),
      n_edges = sum(states != 0L),
      weakly_connected = is_weakly_connected(adj),
      n_topological_orders = length(topo_idx),
      n_signatures = length(signatures),
      signature_set_key = paste(signatures, collapse = ";"),
      lex_first_order = paste(perms[topo_idx[[1L]], ], collapse = "-"),
      lex_first_signature = signature_by_perm[topo_idx[[1L]]],
      markov_key = markov_key(adj),
      closure_key = closure_key,
      n_reachability_relations = sum(closure),
      closure_up_to_dual_key = min(closure_key, dual_key),
      stringsAsFactors = FALSE
    )
  }
  result <- do.call(rbind, records[seq_len(kept)])
  rownames(result) <- NULL
  cat(sprintf("  retained %d DAGs\n", nrow(result)))
  result
}

summarize_connected_dags <- function(df) {
  n <- unique(df$n)
  stopifnot(length(n) == 1L)
  work <- df[df$weakly_connected, , drop = FALSE]
  signature_groups <- split(work, work$signature_set_key)

  signature_equal_pairs <- pair_total(table(work$signature_set_key))
  signature_equal_nonmarkov_pairs <- pairs_equal_first_not_second(
    work, "signature_set_key", "markov_key"
  )
  markov_equal_pairs <- pair_total(table(work$markov_key))
  markov_equal_different_signature_pairs <- pairs_equal_first_not_second(
    work, "markov_key", "signature_set_key"
  )
  same_reachability_pairs_formula <- pair_total(table(work$closure_key))

  nonmarkov_same_reachability_pairs <- 0
  nonmarkov_dual_reachability_pairs <- 0
  nonmarkov_other_reachability_pairs <- 0
  for (g in signature_groups) {
    if (nrow(g) < 2L) next
    pairs <- combn(seq_len(nrow(g)), 2L)
    nonmarkov <-
      g$markov_key[pairs[1L, ]] != g$markov_key[pairs[2L, ]]
    same_reachability <-
      g$closure_key[pairs[1L, ]] == g$closure_key[pairs[2L, ]]
    same_up_to_dual <-
      g$closure_up_to_dual_key[pairs[1L, ]] ==
        g$closure_up_to_dual_key[pairs[2L, ]]

    nonmarkov_same_reachability_pairs <-
      nonmarkov_same_reachability_pairs +
      sum(nonmarkov & same_reachability)
    nonmarkov_dual_reachability_pairs <-
      nonmarkov_dual_reachability_pairs +
      sum(nonmarkov & !same_reachability & same_up_to_dual)
    nonmarkov_other_reachability_pairs <-
      nonmarkov_other_reachability_pairs +
      sum(nonmarkov & !same_up_to_dual)
  }

  data.frame(
    n = n,
    n_connected_dags = nrow(work),
    n_signature_set_classes = length(signature_groups),
    mean_dags_per_signature_class = nrow(work) / length(signature_groups),
    signature_equal_pairs = signature_equal_pairs,
    signature_equal_markov_pairs =
      signature_equal_pairs - signature_equal_nonmarkov_pairs,
    signature_equal_nonmarkov_pairs =
      signature_equal_nonmarkov_pairs,
    nonmarkov_same_reachability_pairs =
      nonmarkov_same_reachability_pairs,
    same_reachability_pairs_formula =
      same_reachability_pairs_formula,
    nonmarkov_dual_reachability_pairs =
      nonmarkov_dual_reachability_pairs,
    nonmarkov_other_reachability_pairs =
      nonmarkov_other_reachability_pairs,
    markov_equal_pairs = markov_equal_pairs,
    markov_equal_different_signature_pairs =
      markov_equal_different_signature_pairs,
    stringsAsFactors = FALSE
  )
}

summarize_dags <- function(df) {
  n <- unique(df$n)
  stopifnot(length(n) == 1L)

  sig_counts <- table(df$signature_set_key)
  markov_counts <- table(df$markov_key)
  closure_dual_counts <- table(df$closure_up_to_dual_key)
  lex_counts <- table(df$lex_first_signature)

  sig_pairs <- pair_total(sig_counts)
  markov_pairs <- pair_total(markov_counts)
  closure_dual_pairs <- pair_total(closure_dual_counts)
  lex_pairs <- pair_total(lex_counts)

  sig_nonmarkov <- pairs_equal_first_not_second(
    df, "signature_set_key", "markov_key"
  )
  markov_diff_sig <- pairs_equal_first_not_second(
    df, "markov_key", "signature_set_key"
  )
  sig_diff_closure_dual <- pairs_equal_first_not_second(
    df, "signature_set_key", "closure_up_to_dual_key"
  )
  nondegenerate <- df[df$n_reachability_relations >= 2L, , drop = FALSE]
  nondegenerate_sig_diff_closure_dual <- pairs_equal_first_not_second(
    nondegenerate, "signature_set_key", "closure_up_to_dual_key"
  )
  lex_nonmarkov <- pairs_equal_first_not_second(
    df, "lex_first_signature", "markov_key"
  )

  singleton <- df[df$n_signatures == 1L, , drop = FALSE]
  unavoidable_nonmarkov <- if (nrow(singleton) > 1L) {
    pairs_equal_first_not_second(
      singleton, "signature_set_key", "markov_key"
    )
  } else 0

  signature_groups <- split(df, df$signature_set_key)
  nonmarkov_signature_groups <- vapply(signature_groups, function(g) {
    length(unique(g$markov_key)) > 1L
  }, logical(1))
  n_signature_collision_classes <- sum(nonmarkov_signature_groups)
  n_dags_in_signature_collision_classes <- sum(vapply(
    signature_groups[nonmarkov_signature_groups], nrow, integer(1)
  ))

  singleton_groups <- split(singleton, singleton$signature_set_key)
  strong_collision_groups <- vapply(singleton_groups, function(g) {
    length(unique(g$markov_key)) > 1L
  }, logical(1))
  n_strong_collision_classes <- sum(strong_collision_groups)
  n_dags_in_strong_collision_classes <- sum(vapply(
    singleton_groups[strong_collision_groups], nrow, integer(1)
  ))

  n_possible_single_signatures <- factorial(n) / 2
  unique_order_formula <- factorial(n) *
    2 ^ ((n - 1L) * (n - 2L) / 2)
  unique_order_class_size_formula <-
    2 ^ (1 + (n - 1L) * (n - 2L) / 2)

  by_code <- setNames(seq_len(nrow(df)), as.character(df$graph_code))
  reverse_pairs <- 0
  reverse_nonmarkov <- 0
  reverse_sig_failures <- 0
  for (i in seq_len(nrow(df))) {
    reverse_code <- as.character(df$reverse_graph_code[[i]])
    j <- by_code[[reverse_code]]
    if (is.null(j) || df$graph_code[[i]] >= df$graph_code[[j]]) next
    reverse_pairs <- reverse_pairs + 1
    if (df$markov_key[[i]] != df$markov_key[[j]]) {
      reverse_nonmarkov <- reverse_nonmarkov + 1
    }
    if (df$signature_set_key[[i]] != df$signature_set_key[[j]]) {
      reverse_sig_failures <- reverse_sig_failures + 1
    }
  }

  data.frame(
    n = n,
    n_dags = nrow(df),
    n_markov_classes = length(markov_counts),
    n_possible_single_signatures = n_possible_single_signatures,
    n_signature_set_classes = length(sig_counts),
    n_signature_collision_classes = n_signature_collision_classes,
    n_dags_in_signature_collision_classes =
      n_dags_in_signature_collision_classes,
    n_closure_up_to_dual_classes = length(closure_dual_counts),
    max_signature_class_size = max(sig_counts),
    signature_equal_pairs = sig_pairs,
    signature_equal_nonmarkov_pairs = sig_nonmarkov,
    markov_equal_pairs = markov_pairs,
    markov_equal_different_signature_pairs = markov_diff_sig,
    signature_equal_different_closure_dual_pairs = sig_diff_closure_dual,
    nondegenerate_signature_equal_different_closure_dual_pairs =
      nondegenerate_sig_diff_closure_dual,
    lex_signature_equal_pairs = lex_pairs,
    lex_signature_equal_nonmarkov_pairs = lex_nonmarkov,
    n_unique_topological_order_dags =
      sum(df$n_topological_orders == 1L),
    unique_topological_order_dags_formula = unique_order_formula,
    unique_order_signature_class_size_formula =
      unique_order_class_size_formula,
    n_strong_collision_classes = n_strong_collision_classes,
    n_dags_in_strong_collision_classes =
      n_dags_in_strong_collision_classes,
    unavoidable_nonmarkov_pairs = unavoidable_nonmarkov,
    reversal_pairs = reverse_pairs,
    reversal_nonmarkov_pairs = reverse_nonmarkov,
    reversal_signature_failures = reverse_sig_failures,
    stringsAsFactors = FALSE
  )
}

first_cross_pair <- function(df, group_field, comparison_field,
                             subset_rows = rep(TRUE, nrow(df))) {
  work <- df[subset_rows, , drop = FALSE]
  groups <- split(work, work[[group_field]])
  for (g in groups) {
    values <- unique(g[[comparison_field]])
    if (length(values) < 2L) next
    i <- 1L
    j <- which(g[[comparison_field]] != g[[comparison_field]][[i]])[[1L]]
    return(g[c(i, j), , drop = FALSE])
  }
  NULL
}

example_rows <- function(df) {
  examples <- list()

  add_example <- function(label, pair) {
    if (is.null(pair)) return(invisible(NULL))
    block <- pair[, c(
      "n", "graph_key", "n_edges", "n_topological_orders", "n_signatures",
      "signature_set_key", "lex_first_order", "lex_first_signature",
      "markov_key", "closure_up_to_dual_key"
    )]
    block$example <- label
    block$member <- c("A", "B")
    examples[[length(examples) + 1L]] <<- block
  }

  add_example(
    "same_signature_set_nonmarkov",
    first_cross_pair(df, "signature_set_key", "markov_key")
  )
  add_example(
    "same_signature_set_different_closure_up_to_dual",
    first_cross_pair(
      df, "signature_set_key", "closure_up_to_dual_key"
    )
  )
  add_example(
    "markov_equivalent_different_signature_set",
    first_cross_pair(df, "markov_key", "signature_set_key")
  )
  add_example(
    "unavoidable_single_signature_nonmarkov",
    first_cross_pair(
      df, "signature_set_key", "markov_key", df$n_signatures == 1L
    )
  )

  if (!length(examples)) return(NULL)
  result <- do.call(rbind, examples)
  result <- result[, c("example", "member", setdiff(names(result), c("example", "member")))]
  rownames(result) <- NULL
  result
}

expected_dag_counts <- c(`2` = 3L, `3` = 25L, `4` = 543L, `5` = 29281L)
expected_markov_class_counts <- c(`2` = 2L, `3` = 11L, `4` = 185L, `5` = 8782L)
expected_connected_dag_counts <- c(`2` = 2L, `3` = 18L, `4` = 446L, `5` = 26430L)
expected_connected_signature_classes <- c(`2` = 1L, `3` = 6L, `4` = 73L, `5` = 1530L)
expected_connected_nonmarkov_pairs <- c(`2` = 0, `3` = 15, `4` = 1915, `5` = 743535)
all_dags <- list()
all_summaries <- list()
all_connected_summaries <- list()
all_examples <- list()

for (n in 2:5) {
  dags <- enumerate_dags(n)
  stopifnot(nrow(dags) == expected_dag_counts[[as.character(n)]])
  summary <- summarize_dags(dags)
  fiber_audit <- audit_reachability_fibers(dags)
  summary <- cbind(summary, fiber_audit)
  connected_summary <- summarize_connected_dags(dags)
  stopifnot(
    summary$n_markov_classes ==
      expected_markov_class_counts[[as.character(n)]],
    summary$reversal_signature_failures == 0,
    summary$nondegenerate_signature_equal_different_closure_dual_pairs == 0,
    summary$n_unique_topological_order_dags ==
      summary$unique_topological_order_dags_formula,
    connected_summary$n_connected_dags ==
      expected_connected_dag_counts[[as.character(n)]],
    connected_summary$n_signature_set_classes ==
      expected_connected_signature_classes[[as.character(n)]],
    connected_summary$signature_equal_nonmarkov_pairs ==
      expected_connected_nonmarkov_pairs[[as.character(n)]],
    connected_summary$nonmarkov_same_reachability_pairs ==
      connected_summary$same_reachability_pairs_formula,
    summary$reachability_fiber_size_failures == 0,
    summary$reachability_edge_interval_failures == 0,
    connected_summary$nonmarkov_other_reachability_pairs == 0
  )
  examples <- example_rows(dags)

  all_dags[[as.character(n)]] <- dags
  all_summaries[[as.character(n)]] <- summary
  all_connected_summaries[[as.character(n)]] <- connected_summary
  all_examples[[as.character(n)]] <- examples

  if (write_full_audit) {
    write.csv(
      dags,
      file.path(output_dir, sprintf("signature_equivalence_dags_n%d.csv", n)),
      row.names = FALSE
    )
  }
}

summary_df <- do.call(rbind, all_summaries)
rownames(summary_df) <- NULL
connected_summary_df <- do.call(rbind, all_connected_summaries)
rownames(connected_summary_df) <- NULL
examples_df <- do.call(rbind, all_examples)
rownames(examples_df) <- NULL

if (write_full_audit) {
  write.csv(
    summary_df,
    file.path(output_dir, "signature_equivalence_summary.csv"),
    row.names = FALSE
  )
  write.csv(
    connected_summary_df,
    file.path(output_dir, "signature_equivalence_connected_summary.csv"),
    row.names = FALSE
  )
  write.csv(
    examples_df,
    file.path(output_dir, "signature_equivalence_examples.csv"),
    row.names = FALSE
  )
}

table1_df <- data.frame(
  n = connected_summary_df$n,
  connected_dags = connected_summary_df$n_connected_dags,
  signature_classes = connected_summary_df$n_signature_set_classes,
  nonmarkov_collisions = connected_summary_df$signature_equal_nonmarkov_pairs,
  same_closure = connected_summary_df$nonmarkov_same_reachability_pairs,
  dual_closure = connected_summary_df$nonmarkov_dual_reachability_pairs,
  other = connected_summary_df$nonmarkov_other_reachability_pairs
)
table1_df <- table1_df[table1_df$n >= 3L, , drop = FALSE]
write.csv(
  table1_df,
  file.path(output_dir, "table1.csv"),
  row.names = FALSE
)

format_count <- function(x) {
  format(x, big.mark = ",", scientific = FALSE, trim = TRUE)
}
table1_rows <- vapply(seq_len(nrow(table1_df)), function(i) {
  values <- format_count(unlist(table1_df[i, ], use.names = FALSE))
  paste0(paste(values, collapse = " & "), " \\\\")
}, character(1))
writeLines(table1_rows, file.path(output_dir, "table1_rows.tex"))

cat("\nSummary:\n")
print(summary_df, row.names = FALSE)
cat("\nConnected-DAG summary:\n")
print(connected_summary_df, row.names = FALSE)
cat(sprintf("\nOutputs written to %s\n", output_dir))
