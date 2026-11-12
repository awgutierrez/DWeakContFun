import MetricFunctional

noncomputable section

open Set Filter Topology

universe u

variable {K : Type*}
variable [TopologicalSpace K]
variable [CompactSpace K]
variable [T2Space K]
variable [Nonempty K]

set_option linter.style.whitespace false

/-!
# d-weak convergence

This module contains the abstract counterexample mechanism.  Pairwise
disjoint supports force every metric functional to be negative at most once;
therefore its values are eventually non-negative and have non-negative
liminf.  The module also packages the resulting d-weak convergence with
unbounded norm growth.
-/

/-! Main Theorem -/
/-! Metric Functional is Negative at Most One fn-/
/-!
For a metric functional obtained as a pointwise limit of internal metric functionals,
negativity on two distinct sequence terms would eventually force one internal
approximant to be negative on both, contradicting the internal support lemma.
-/
omit [T2Space K] in
lemma metric_functional_negative_at_most_one
    (f : ℕ → C(K, ℝ))
    (hdisjoint :
      ∀ ⦃m n : ℕ⦄, m ≠ n →
        Disjoint (Function.support (f m)) (Function.support (f n)))
    (h : C(K, ℝ) → ℝ)
    (hmetric : IsMetricFunctional (0 : C(K, ℝ)) h) :
    ∀ ⦃m n : ℕ⦄,
      h (f m) < 0 →
      h (f n) < 0 →
      m = n := by
  intro m n hm hn
  by_contra hmn
  obtain ⟨w⟩ := hmetric
  let ε : ℝ := min (-h (f m)) (-h (f n)) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    have hm' : 0 < -h (f m) := by
      linarith
    have hn' : 0 < -h (f n) := by
      linarith
    exact half_pos (lt_min hm' hn')
  obtain ⟨i, him, hin⟩ :=
    metric_functional_two_point_approx
      w (f m) (f n) ε hε
  have him_upper :
      (dist (f m) (w.w i) - dist 0 (w.w i)) - h (f m) < ε :=
    (abs_lt.mp him).2
  have hin_upper :
      (dist (f n) (w.w i) - dist 0 (w.w i)) - h (f n) < ε :=
    (abs_lt.mp hin).2
  have hεm :
      ε ≤ -h (f m) / 2 := by
    dsimp [ε]
    exact div_le_div_of_nonneg_right
      (min_le_left _ _) (by norm_num)
  have hεn :
      ε ≤ -h (f n) / 2 := by
    dsimp [ε]
    exact div_le_div_of_nonneg_right
      (min_le_right _ _) (by norm_num)
  have him_neg :
      dist (f m) (w.w i) - dist 0 (w.w i) < 0 := by
    linarith
  have hin_neg :
      dist (f n) (w.w i) - dist 0 (w.w i) < 0 := by
    linarith
  have him_norm :
      ‖f m - w.w i‖ - ‖w.w i‖ < 0 := by
    simpa [dist_eq_norm] using him_neg
  have hin_norm :
      ‖f n - w.w i‖ - ‖w.w i‖ < 0 := by
    simpa [dist_eq_norm] using hin_neg
  have hmn' : m = n :=
    internal_negative_at_most_one
      f hdisjoint (w.w i) him_norm hin_norm
  exact hmn hmn'

/-! A sequence of real numbers is eventually non-negative if it
is negative at most once. -/
/-! A real sequence that is negative at most once is eventually nonnegative. -/
lemma eventually_nonneg_of_negative_at_most_one
    (a : ℕ → ℝ)
    (hatmost :
      ∀ ⦃m n : ℕ⦄, a m < 0 → a n < 0 → m = n) :
    ∃ N, ∀ n ≥ N, 0 ≤ a n := by
  by_cases hneg : ∃ m : ℕ, a m < 0
  · obtain ⟨m, hm⟩ := hneg
    refine ⟨m + 1, ?_⟩
    intro n hn
    by_contra hnonneg
    have hnneg : a n < 0 := lt_of_not_ge hnonneg
    have hmn : m = n := hatmost hm hnneg
    have hnm : n ≠ m := by
      intro hnm
      subst hnm
      omega
    exact hnm hmn.symm
  · refine ⟨0, ?_⟩
    intro n hn
    by_contra hnonneg
    have hnneg : a n < 0 := lt_of_not_ge hnonneg
    exact hneg ⟨n, hnneg⟩

/-! Liminf is non-negative if the sequence is eventually non-negative -/
/-! An eventually nonnegative real sequence has nonnegative liminf. -/
lemma liminf_nonneg_of_eventually_nonneg
    (a : ℕ → ℝ)
    (ha : ∃ N, ∀ n ≥ N, 0 ≤ a n) :
    0 ≤ Filter.liminf a atTop := by
  let S : Set ℝ :=
    {b : ℝ | ∀ᶠ n in (atTop : Filter ℕ), b ≤ a n}
  have hzero : (0 : ℝ) ∈ S := by
    dsimp [S]
    obtain ⟨N, hN⟩ := ha
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  rw [Filter.liminf_eq]
  change 0 ≤ sSup S
  by_cases hbounded : BddAbove S
  · exact le_csSup hbounded hzero
  · rw [csSup_of_not_bddAbove hbounded]
    simp

/-!
Combining the metric-functional negativity lemma with the previous sequence lemma
gives eventual nonnegativity of every metric-functional evaluation on the spike
sequence.
-/
omit [T2Space K] in
lemma metric_functional_eventually_nonneg
    (f : ℕ → C(K, ℝ))
    (hdisjoint :
      ∀ ⦃m n : ℕ⦄, m ≠ n →
        Disjoint (Function.support (f m)) (Function.support (f n)))
    (h : C(K, ℝ) → ℝ)
    (hmetric : IsMetricFunctional (0 : C(K, ℝ)) h) :
    ∃ N, ∀ n ≥ N, 0 ≤ h (f n) := by
  apply eventually_nonneg_of_negative_at_most_one
  intro m n hm hn
  exact metric_functional_negative_at_most_one
    f hdisjoint h hmetric hm hn

/-!
Every metric functional therefore has nonnegative liminf along a sequence with
pairwise disjoint supports.
-/
omit [T2Space K] in
lemma metric_functional_liminf_nonneg
    (f : ℕ → C(K, ℝ))
    (hdisjoint :
      ∀ ⦃m n : ℕ⦄, m ≠ n →
        Disjoint (Function.support (f m)) (Function.support (f n)))
    (h : C(K, ℝ) → ℝ)
    (hmetric : IsMetricFunctional (0 : C(K, ℝ)) h) :
    0 ≤ Filter.liminf (fun n => h (f n)) atTop := by
  apply liminf_nonneg_of_eventually_nonneg
  exact metric_functional_eventually_nonneg
    f hdisjoint h hmetric


/-! d-weak convergence -/

/-! Definition of d-weak convergence used in the project. -/
def DWeaklyConverges
    {X : Type u} [MetricSpace X]
    (o : X) (x : ℕ → X) (z : X) : Prop :=
  ∀ h : X → ℝ,
    IsMetricFunctional o h →
      h z ≤ Filter.liminf (fun n => h (x n)) atTop


/-!
Pairwise disjoint supports imply d-weak convergence to the zero function: every
metric functional is zero at the base point and has nonnegative liminf along the
sequence.
-/
omit [T2Space K] in
lemma dWeaklyConverges_of_disjoint_supports
    (f : ℕ → C(K, ℝ))
    (hdisjoint :
      ∀ ⦃m n : ℕ⦄, m ≠ n →
        Disjoint (Function.support (f m)) (Function.support (f n))) :
    DWeaklyConverges (0 : C(K, ℝ)) f 0 := by
  intro h hmetric
  have hzero : h (0 : C(K, ℝ)) = 0 :=
    metric_functional_basepoint hmetric
  have hliminf :
      0 ≤ Filter.liminf (fun n => h (f n)) atTop := by
    exact metric_functional_liminf_nonneg
      f hdisjoint h hmetric
  rw [hzero]
  exact hliminf
