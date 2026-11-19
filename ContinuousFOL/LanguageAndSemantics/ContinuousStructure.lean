/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.9; vision.md page 10
-/
module

public import ContinuousFOL.LanguageAndSemantics.MetricPreStructure
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Completion

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- A continuous `𝓛`-structure: metric pre-structure where `d^𝔐` is a *complete metric*
    (Definition 5.9). -/
structure ContinuousStructure (LM : MetricSignature) extends MetricPreStructure LM where
  metricSpace   : MetricSpace Carrier
  dist_eq       : ∀ a b, @Dist.dist Carrier metricSpace.toDist a b = distVal a b
  completeSpace : @CompleteSpace Carrier metricSpace.toUniformSpace

end ContinuousFOL
