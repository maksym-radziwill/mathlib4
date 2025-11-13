/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Meromorphic.Basic

universe u_1 u_2
variable {𝕜 : Type u_1} {E : Type u_2} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma MeromorphicAt.slope {f : 𝕜 → E} {a c : 𝕜}
  (analytic : AnalyticAt 𝕜 f c) : MeromorphicAt (slope f a) c :=
  ((MeromorphicAt.id c).sub (MeromorphicAt.const a c)).inv.smul
    ((analytic.meromorphicAt).sub (MeromorphicAt.const (f a) c))

lemma MeromorphicAt.dslope {f : 𝕜 → E} {a c : 𝕜}
  (analytic : AnalyticAt 𝕜 f c) : MeromorphicAt (dslope f a) c := by
  classical exact MeromorphicAt.update (slope analytic) a (deriv f a)

lemma ContinuousAt.dslope {f : 𝕜 → E} {a c : 𝕜}
  (analytic : AnalyticAt 𝕜 f c) : ContinuousAt (dslope f a) c := by
  by_cases h : c = a
  · rw [← h, continuousAt_dslope_same]; exact analytic.differentiableAt
  · rw [continuousAt_dslope_of_ne h]; exact analytic.continuousAt

theorem AnalyticAt.dslope {f : 𝕜 → E} {a c : 𝕜}
  (analytic : AnalyticAt 𝕜 f c) : AnalyticAt 𝕜 (dslope f a) c :=
  MeromorphicAt.analyticAt (MeromorphicAt.dslope analytic) (ContinuousAt.dslope analytic)

theorem AnalyticOnNhd.dslope {f : 𝕜 → E} {s : Set 𝕜} {a : 𝕜}
  (analytic : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (dslope f a) s :=
  fun x hx => AnalyticAt.dslope (analytic x hx)
  