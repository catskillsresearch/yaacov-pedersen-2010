/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import ContinuousFOL

/-!
# Palomar Solution

Imports the `ContinuousFOL/` library. The comparator matches the compared
declarations named in `Challenge.lean` / `comparator.json` against these
proved definitions and theorems:

* Theorem 7.2: `soundness_pre`, `soundness_metric_full`
* Theorem 9.4: `henkin_model_existence`, `henkin_model_existence_metric`
* Theorem 9.5: `completeness_pre`, `completeness_metric`
* Corollary 9.6: `approximated_strong_completeness_pre`,
  `approximated_strong_completeness_metric`
* Corollary 9.8: `pavelka_completeness_pre`, `pavelka_completeness_metric`
* Corollary 9.11: `complete_re_theory_decidable`
* Corollary 9.12: `compactness_pre`, `compactness_metric`
-/
@[expose] public section
