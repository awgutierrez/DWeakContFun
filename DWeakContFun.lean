import NormSupport
import MetricFunctional
import DWeak
import Tent

/-!
The explicit spike sequence d-weakly converges to zero while its sup norms
are unbounded. This is the concrete counterexample assembled from the
abstract metric-functional argument in `DWeak` and the tent construction in
`Tent`.
-/
theorem spike_counterexample :
    DWeaklyConverges
        (0 : C(Set.Icc (0 : ℝ) 1, ℝ))
        spike
        0 ∧
      ¬ ∃ C : ℝ, ∀ n, ‖spike n‖ ≤ C := by
  constructor
  · exact dWeaklyConverges_of_disjoint_supports
      spike
      spike_disjoint_supports
  · intro hbounded
    obtain ⟨C, hC⟩ := hbounded
    obtain ⟨n, hn⟩ := exists_nat_gt C
    have hupper : ‖spike n‖ ≤ C := hC n
    have hlower : (n : ℝ) ≤ ‖spike n‖ := spike_norm_ge n
    linarith



/--
Strengthened version of Theorem 1.3.

The spike sequence d-weakly converges to zero,
while its sup norms tend to positive infinity.
-/
theorem spike_counterexample_strong :
    DWeaklyConverges
        (0 : C(Set.Icc (0 : ℝ) 1, ℝ))
        spike
        0 ∧
      Filter.Tendsto
        (fun n : ℕ => ‖spike n‖)
        Filter.atTop
        Filter.atTop := by
  constructor
  · exact dWeaklyConverges_of_disjoint_supports
      spike
      spike_disjoint_supports
  · apply Filter.tendsto_atTop.2
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hNreal : b ≤ (n : ℝ) := by
      calc
        b ≤ (N : ℝ) := le_of_lt hN
        _ ≤ (n : ℝ) := by exact_mod_cast hn
    exact hNreal.trans (spike_norm_ge n)
