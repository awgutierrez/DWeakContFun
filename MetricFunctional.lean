import NormSupport
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Basic

noncomputable section

open Set Filter Topology

/-!
# Metric functionals

This module formalizes metric functionals as pointwise limits of nets of
internal metric functionals.  It proves basepoint vanishing and the
simultaneous two-point approximation property used in the main argument.
-/

/-! Formalization of metric functionals -/
universe u

structure MetricFunctionalWitness
    {X : Type u} [MetricSpace X]
    (o : X) (h : X → ℝ) where
  ι : Type u
  instPreorder : Preorder ι
  instNonempty : Nonempty ι
  instDirected : IsDirected ι (· ≤ ·)
  w : ι → X
  tendsto :
    ∀ x : X,
      Tendsto
        (fun i => dist x (w i) - dist o (w i))
        atTop
        (𝓝 (h x))

def IsMetricFunctional
    {X : Type u} [MetricSpace X]
    (o : X) (h : X → ℝ) : Prop :=
  Nonempty (MetricFunctionalWitness o h)

/-! Every metric functional vanishes at its base point. -/

/-! Every metric functional vanishes at its chosen base point, because every internal approximant vanishes there and the convergence is pointwise. -/
lemma metric_functional_basepoint
    {X : Type u} [MetricSpace X]
    {o : X} {h : X → ℝ}
    (hmetric : IsMetricFunctional o h) :
    h o = 0 := by

  obtain ⟨w⟩ := hmetric

  letI := w.instPreorder
  letI := w.instNonempty
  letI := w.instDirected

  have hlim :
      Tendsto
        (fun i : w.ι => dist o (w.w i) - dist o (w.w i))
        atTop
        (𝓝 (h o)) := by
    exact w.tendsto o

  have hconst :
      Tendsto
        (fun _ : w.ι => (0 : ℝ))
        atTop
        (𝓝 0) :=
    tendsto_const_nhds

  have hlim' :
      Tendsto
        (fun _ : w.ι => (0 : ℝ))
        atTop
        (𝓝 (h o)) := by
    simpa using hlim

  exact tendsto_nhds_unique hlim' hconst

/-! Two-point approximation for metric functionals -/
/-! A metric functional can be approximated simultaneously at any two prescribed points by one internal metric functional. Directedness lets us combine the two eventual convergence conditions. -/
lemma metric_functional_two_point_approx
    {X : Type u} [MetricSpace X]
    {o : X} {h : X → ℝ}
    (w : MetricFunctionalWitness o h)
    (x₁ x₂ : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ i : w.ι,
      dist (dist x₁ (w.w i) - dist o (w.w i)) (h x₁) < ε ∧
      dist (dist x₂ (w.w i) - dist o (w.w i)) (h x₂) < ε := by

  letI := w.instPreorder
  letI := w.instNonempty
  letI := w.instDirected

  have hev₁ :
      ∀ᶠ i in (atTop : Filter w.ι),
        dist (dist x₁ (w.w i) - dist o (w.w i)) (h x₁) < ε := by
    exact Metric.tendsto_nhds.mp (w.tendsto x₁) ε hε

  have hev₂ :
      ∀ᶠ i in (atTop : Filter w.ι),
        dist (dist x₂ (w.w i) - dist o (w.w i)) (h x₂) < ε := by
    exact Metric.tendsto_nhds.mp (w.tendsto x₂) ε hε

  have hev :
      ∀ᶠ i in (atTop : Filter w.ι),
        dist (dist x₁ (w.w i) - dist o (w.w i)) (h x₁) < ε ∧
        dist (dist x₂ (w.w i) - dist o (w.w i)) (h x₂) < ε :=
    hev₁.and hev₂

  obtain ⟨i, hi⟩ := hev.exists

  exact ⟨i, hi⟩
