import DWeak
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Basic

noncomputable section

open Set Filter Topology

/-!
# Continuous tent functions and the explicit spike sequence

This module constructs pairwise-disjoint tent intervals in [0,1], scales the
corresponding continuous tents so that the nth spike has value n at its
midpoint, and proves the support and norm estimates needed for the
abstract d-weak convergence argument.
-/

/-! Continuous tent function -/
/-! The scalar tent profile x ↦ max 0 (min (x-a) (b-x)) is continuous. -/
lemma continuous_tent
    (a b : ℝ)
    (_hab : a ≤ b) :
    Continuous (fun x : ℝ => max 0 (min (x - a) (b - x))) := by
  have h1 : Continuous (fun x : ℝ => (0 : ℝ)) :=
    continuous_const
  have h2 : Continuous (fun x : ℝ => x - a) := by
    fun_prop
  have h3 : Continuous (fun x : ℝ => b - x) := by
    fun_prop
  have hmin :
      Continuous (fun x : ℝ => min (x - a) (b - x)) :=
    h2.min h3
  exact h1.max hmin


def tent
    (a b : ℝ)
    (hab : a ≤ b) :
    C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ContinuousMap.mk
    (fun x : Set.Icc (0 : ℝ) 1 =>
      max 0 (min (x.1 - a) (b - x.1)))
    (by
      exact (continuous_tent a b hab).comp continuous_subtype_val)

/-! Evaluation of the ContinuousMap tent is exactly the defining scalar tent formula. -/
lemma tent_apply
    (a b : ℝ)
    (hab : a ≤ b)
    (x : Set.Icc (0 : ℝ) 1) :
    tent a b hab x =
      max 0 (min (x.1 - a) (b - x.1)) := by
  rfl

/-! The tent function is pointwise nonnegative. -/
lemma tent_nonneg
    (a b : ℝ)
    (hab : a ≤ b)
    (x : Set.Icc (0 : ℝ) 1) :
    0 ≤ tent a b hab x := by
  rw [tent_apply]
  exact le_max_left _ _


/-! If the norm of the nth term is at least n, then the sequence of norms is unbounded. -/
lemma unbounded_of_norm_ge
    (f : ℕ → C(Set.Icc (0 : ℝ) 1, ℝ))
    (hnorm : ∀ n, (n : ℕ) ≤ ‖f n‖) :
    ¬ ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hupper : ‖f n‖ ≤ C := hC n
  have hlower : (n : ℝ) ≤ ‖f n‖ := hnorm n
  linarith


/-! Outside the closed interval [a,b], the tent function vanishes. -/
lemma tent_eq_zero_of_not_mem_Icc
    (a b : ℝ)
    (hab : a ≤ b)
    (x : Set.Icc (0 : ℝ) 1)
    (hx : x.1 ∉ Set.Icc a b) :
    tent a b hab x = 0 := by
  rw [tent_apply]
  by_cases hxa : x.1 < a
  · have hleft : x.1 - a ≤ 0 := by
      linarith
    have hmin : min (x.1 - a) (b - x.1) ≤ 0 := by
      exact le_trans (min_le_left _ _) hleft
    exact max_eq_left hmin
  · have hax : a ≤ x.1 := by
      linarith
    have hbx : b < x.1 := by
      by_contra hnot
      have hxb : x.1 ≤ b := by
        linarith
      exact hx ⟨hax, hxb⟩
    have hright : b - x.1 ≤ 0 := by
      linarith
    have hmin : min (x.1 - a) (b - x.1) ≤ 0 := by
      exact le_trans (min_le_right _ _) hright
    exact max_eq_left hmin


/-! The support of a tent is contained in the preimage of its defining interval [a,b]. -/
lemma tent_support_subset
    (a b : ℝ) (hab : a ≤ b) :
    Function.support (tent a b hab) ⊆
      (fun x : Set.Icc (0 : ℝ) 1 => x.1) ⁻¹' Set.Icc a b := by
  intro x hx
  by_contra hnot
  have hnot' : x.1 ∉ Set.Icc a b := by
    exact hnot
  have hz : tent a b hab x = 0 :=
    tent_eq_zero_of_not_mem_Icc a b hab x hnot'
  rw [Function.mem_support] at hx
  exact hx hz


def tentLeft (n : ℕ) : ℝ :=
  1 / (2 * n + 2)

def tentRight (n : ℕ) : ℝ :=
  1 / (2 * n + 1)

def tentInterval (n : ℕ) : Set ℝ :=
  Set.Icc (tentLeft n) (tentRight n)


/-! The endpoints defining each tent interval are ordered: 1/(2n+2) ≤ 1/(2n+1). -/
lemma tentLeft_le_tentRight (n : ℕ) :
    tentLeft n ≤ tentRight n := by
  unfold tentLeft tentRight
  have hpos : (0 : ℝ) < 2 * n + 1 := by
    positivity
  apply one_div_le_one_div_of_le hpos
  norm_num


/-! Every tent interval lies inside the ambient domain [0,1]. -/
lemma tentInterval_subset_Icc (n : ℕ) :
    tentInterval n ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  rcases hx with ⟨hx_left, hx_right⟩
  constructor
  · unfold tentLeft at hx_left
    have hpos : (0 : ℝ) < 1 / (2 * n + 2) := by
      positivity
    exact le_trans (le_of_lt hpos) hx_left
  · unfold tentRight at hx_right
    have hdenom : (1 : ℝ) ≤ 2 * n + 1 := by
      norm_num
    have hle :
        1 / (2 * n + 1) ≤ (1 : ℝ) := by
      simpa using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdenom)
    exact le_trans hx_right hle


/-! If m<n, then the right endpoint of the nth interval lies strictly to the left of the left endpoint of the mth interval. -/
lemma tentRight_lt_tentLeft_of_lt
    {m n : ℕ} (hmn : m < n) :
    tentRight n < tentLeft m := by
  unfold tentRight tentLeft
  apply one_div_lt_one_div_of_lt
    (by positivity : (0 : ℝ) < 2 * m + 2)
  have hmn' : 2 * m + 2 < 2 * n + 1 := by
    omega
  exact_mod_cast hmn'


/-! If m<n, the corresponding tent intervals are disjoint. -/
lemma tentInterval_disjoint_of_lt
    {m n : ℕ} (hmn : m < n) :
    Disjoint (tentInterval n) (tentInterval m) := by
  rw [Set.disjoint_left]
  intro x hx_n hx_m
  have hsep : tentRight n < tentLeft m :=
    tentRight_lt_tentLeft_of_lt hmn
  have h1 : x ≤ tentRight n := hx_n.2
  have h2 : tentLeft m ≤ x := hx_m.1
  linarith


/-! The tent intervals are pairwise disjoint for distinct indices. -/
lemma tentInterval_disjoint
    {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (tentInterval m) (tentInterval n) := by
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · exact (tentInterval_disjoint_of_lt hmn).symm
  · exact tentInterval_disjoint_of_lt hnm

/- Spike function -/
def spike (n : ℕ) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (2 * (n : ℝ) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2)) •
    tent (tentLeft n) (tentRight n) (tentLeft_le_tentRight n)


/- Norm lower bound -/

def tentMid (n : ℕ) : ℝ :=
  (tentLeft n + tentRight n) / 2

/-! The midpoint of each tent interval lies in the ambient domain [0,1]. -/
lemma tentMid_mem_Icc (n : ℕ) :
    tentMid n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold tentMid
  have hle : tentLeft n ≤ tentRight n :=
    tentLeft_le_tentRight n
  have hleft : (0 : ℝ) ≤ tentLeft n := by
    unfold tentLeft
    positivity
  have hright : tentRight n ≤ (1 : ℝ) := by
    have hx : tentRight n ∈ Set.Icc (0 : ℝ) 1 := by
      apply tentInterval_subset_Icc n
      exact ⟨hle, le_rfl⟩
    exact hx.2
  constructor <;> linarith

/-! At the midpoint of its interval, the tent reaches half the interval length. -/
lemma tent_at_mid
    (n : ℕ) :
    tent (tentLeft n) (tentRight n) (tentLeft_le_tentRight n)
        ⟨tentMid n, tentMid_mem_Icc n⟩ =
      (tentRight n - tentLeft n) / 2 := by
  rw [tent_apply]
  have hmid_left :
      tentMid n - tentLeft n =
        (tentRight n - tentLeft n) / 2 := by
    unfold tentMid
    ring
  have hright_mid :
      tentRight n - tentMid n =
        (tentRight n - tentLeft n) / 2 := by
    unfold tentMid
    ring
  rw [hmid_left, hright_mid]
  have hnonneg :
      0 ≤ (tentRight n - tentLeft n) / 2 := by
    have hle : tentLeft n ≤ tentRight n :=
      tentLeft_le_tentRight n
    linarith
  rw [min_self]
  exact max_eq_right hnonneg


/-! The chosen scalar factor normalizes the nth tent so that its value at the midpoint is exactly n. -/
lemma spike_at_mid
    (n : ℕ) :
    spike n ⟨tentMid n, tentMid_mem_Icc n⟩ = (n : ℝ) := by
  simp [spike, tent_at_mid]
  dsimp [tentRight, tentLeft]
  field_simp
  ring


/- ||spike n|| ≥ n -/
/-! Since the nth spike takes the value n somewhere, its sup norm is at least n. -/
lemma spike_norm_ge
    (n : ℕ) :
    (n : ℕ) ≤ ‖spike n‖ := by
  have hpoint :
      ‖spike n ⟨tentMid n, tentMid_mem_Icc n⟩‖ ≤ ‖spike n‖ :=
    ContinuousMap.norm_coe_le_norm
      (spike n)
      ⟨tentMid n, tentMid_mem_Icc n⟩
  rw [spike_at_mid] at hpoint
  norm_num at hpoint
  exact hpoint

def spikeInterval
    (n : ℕ) : Set (Set.Icc (0 : ℝ) 1) :=
  (fun x : Set.Icc (0 : ℝ) 1 => x.1) ⁻¹' tentInterval n


/-Suport of the spike function -/
/-! The support of each scaled spike is contained in its corresponding subtype interval. -/
lemma spike_support_subset
    (n : ℕ) :
    Function.support (spike n) ⊆ spikeInterval n := by
  intro x hx
  have hx_tent :
      tent (tentLeft n) (tentRight n) (tentLeft_le_tentRight n) x ≠ 0 := by
    intro hzero
    apply hx
    simp [spike, hzero]
  exact
    tent_support_subset
      (tentLeft n)
      (tentRight n)
      (tentLeft_le_tentRight n)
      hx_tent

/-! The subtype versions of the tent intervals remain pairwise disjoint. -/
lemma spikeInterval_disjoint
    {m n : ℕ} (hmn : m ≠ n) :
    Disjoint (spikeInterval m) (spikeInterval n) := by
  rw [Set.disjoint_left]
  intro x hxm hxn
  have hxm' :
      x.1 ∈ tentInterval m :=
    hxm
  have hxn' :
      x.1 ∈ tentInterval n :=
    hxn
  have hdis :
      Disjoint (tentInterval m) (tentInterval n) :=
    tentInterval_disjoint hmn
  exact Set.disjoint_left.1 hdis hxm' hxn'


/-! The spike supports are pairwise disjoint, by containment in the pairwise disjoint subtype intervals. -/
lemma spike_disjoint_supports :
    ∀ ⦃m n : ℕ⦄, m ≠ n →
      Disjoint
        (Function.support (spike m))
        (Function.support (spike n)) := by
  intro m n hmn
  have hdisjoint :
      ∀ ⦃m n : ℕ⦄, m ≠ n →
        Disjoint (spikeInterval m) (spikeInterval n) := by
    intro m n hmn
    exact spikeInterval_disjoint hmn
  exact
    (disjoint_supports_of_subset
      spike
      spikeInterval
      spike_support_subset
      hdisjoint) hmn
