import QAELean.QuantumPhaseEstimation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section

open scoped BigOperators Topology
open Filter

namespace QAE
namespace QPE

/-- Real-valued cotangent Mittag-Leffler expansion obtained from Mathlib's complex
`cot_series_rep'` by taking real parts. -/
lemma real_cot_series_rep' {z : ℝ} (hz : (z : ℂ) ∈ Complex.integerComplement) :
    Real.pi * Real.cot (Real.pi * z) - 1 / z =
      ∑' n : ℕ, (1 / (z - ((n + 1 : ℕ) : ℝ)) + 1 / (z + ((n + 1 : ℕ) : ℝ))) := by
  have hc := cot_series_rep' (x := (z : ℂ)) hz
  have hs : Summable fun n : ℕ =>
      (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) := by
    exact summable_cotTerm hz
  have hmap := ContinuousLinearMap.map_tsum Complex.reCLM hs
  have hre : (((Real.pi : ℂ) * (((Real.pi : ℂ) * (z : ℂ))).cot - 1 / (z : ℂ))).re =
      ∑' n : ℕ, Complex.reCLM (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) := by
    rw [← hmap]
    exact congrArg Complex.re hc
  have hleft : (((Real.pi : ℂ) * (((Real.pi : ℂ) * (z : ℂ))).cot - 1 / (z : ℂ))).re =
      Real.pi * Real.cot (Real.pi * z) - 1 / z := by
    have harg : ((Real.pi : ℂ) * (z : ℂ)) = ((Real.pi * z : ℝ) : ℂ) := by
      simp [Complex.ofReal_mul]
    have hleftC : (Real.pi : ℂ) * (((Real.pi : ℂ) * (z : ℂ))).cot - 1 / (z : ℂ) =
        ((Real.pi * Real.cot (Real.pi * z) - 1 / z : ℝ) : ℂ) := by
      rw [harg, ← Complex.ofReal_cot]
      simp [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_inv, one_div]
    change (((Real.pi : ℂ) * (((Real.pi : ℂ) * (z : ℂ))).cot - 1 / (z : ℂ))).re =
      ((Real.pi * Real.cot (Real.pi * z) - 1 / z : ℝ) : ℂ).re
    exact congrArg Complex.re hleftC
  rw [hleft] at hre
  rw [show (∑' n : ℕ, Complex.reCLM (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1)))) =
      ∑' n : ℕ, (1 / (z - ((n + 1 : ℕ) : ℝ)) + 1 / (z + ((n + 1 : ℕ) : ℝ))) by
        apply tsum_congr
        intro n
        have hcomplex :
            1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1)) =
              ((1 / (z - ((n + 1 : ℕ) : ℝ)) +
                1 / (z + ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
          have hsub : (z : ℂ) - (n + 1) = ((z - ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
            norm_num
          have hadd : (z : ℂ) + (n + 1) = ((z + ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
            norm_num
          rw [hsub, hadd]
          simp [one_div, Complex.ofReal_inv]
        change (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))).re =
          ((1 / (z - ((n + 1 : ℕ) : ℝ)) +
            1 / (z + ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ).re
        exact congrArg Complex.re hcomplex] at hre
  exact hre

lemma bhmtTanOddTail_term_bound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (n : ℕ) :
    1 / (((2 * (n + 2) - 1 : ℕ) : ℝ) ^ 2 - u ^ 2) ≤
      1 / (2 * (1 + u ^ 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
  have hu1sq : u ^ 2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one, abs_of_nonneg hu0]
    exact hu1
  have hleftpos : 0 < (((2 * (n + 2) - 1 : ℕ) : ℝ) ^ 2 - u ^ 2) := by
    have hnNat : 1 ≤ 2 * (n + 2) - 1 := by omega
    have hn : (1 : ℝ) ≤ ((2 * (n + 2) - 1 : ℕ) : ℝ) := by exact_mod_cast hnNat
    have hsquare : (1 : ℝ) ≤ ((2 * (n + 2) - 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (((2 * (n + 2) - 1 : ℕ) : ℝ)), hn]
    nlinarith
  have hrightpos : 0 < 2 * (1 + u ^ 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    positivity
  rw [one_div_le_one_div hleftpos hrightpos]
  norm_num
  have hmain :
      0 ≤ (2 * (((n + 2 : ℕ) : ℝ) ^ 2) - 2 * ((n + 2 : ℕ) : ℝ) + 1) * (1 - u ^ 2) := by
    have hquad : 0 ≤ 2 * (((n + 2 : ℕ) : ℝ) ^ 2) - 2 * ((n + 2 : ℕ) : ℝ) + 1 := by
      nlinarith [sq_nonneg (((n + 2 : ℕ) : ℝ) - 1 / 2)]
    have hu : 0 ≤ 1 - u ^ 2 := by nlinarith [le_of_lt hu1sq]
    positivity
  nlinarith

lemma bhmtInvNatSuccMulSuccSucc_telescope_aux (n : ℕ) :
    (1 / ((n + 1 : ℕ) : ℝ) - 1 / ((n + 2 : ℕ) : ℝ)) =
      1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ)) := by
  field_simp [show ((n + 1 : ℕ) : ℝ) ≠ 0 by positivity,
    show ((n + 2 : ℕ) : ℝ) ≠ 0 by positivity]
  norm_num

lemma bhmtInvNatSuccMulSuccSucc_sum_telescope (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) =
      1 - 1 / ((N + 1 : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [← bhmtInvNatSuccMulSuccSucc_telescope_aux N]
      field_simp [show ((N + 1 : ℕ) : ℝ) ≠ 0 by positivity,
        show ((N + 2 : ℕ) : ℝ) ≠ 0 by positivity]
      ring_nf

/-- The odd-denominator tail appearing in the tangent partial-fraction proof of the
BHMT `k = 1` core inequality.  Index `n` represents the paper's integer `n + 2`,
so this is the sum over `n ≥ 2`. -/
def bhmtTanOddTail (u : ℝ) (n : ℕ) : ℝ :=
  1 / (((2 * (n + 2) - 1 : ℕ) : ℝ) ^ 2 - u ^ 2)

/-- The real tangent partial-fraction identity used by the shared proof.  This is
kept as a named hypothesis until the remaining bridge from Mathlib's complex
`cot_series_rep` theorem to this real odd-denominator tangent expansion is
formalized. -/
def bhmtTanPartialFractionIdentity (u : ℝ) : Prop :=
  Real.pi * Real.tan (Real.pi * u / 2) =
    4 * u / (1 - u ^ 2) + 4 * u * (∑' n : ℕ, bhmtTanOddTail u n)

lemma bhmtTanOddTail_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (n : ℕ) :
    0 ≤ bhmtTanOddTail u n := by
  unfold bhmtTanOddTail
  have hu1sq : u ^ 2 < 1 := by
    rw [sq_lt_one_iff_abs_lt_one, abs_of_nonneg hu0]
    exact hu1
  have hleftpos : 0 < (((2 * (n + 2) - 1 : ℕ) : ℝ) ^ 2 - u ^ 2) := by
    have hnNat : 1 ≤ 2 * (n + 2) - 1 := by omega
    have hn : (1 : ℝ) ≤ ((2 * (n + 2) - 1 : ℕ) : ℝ) := by exact_mod_cast hnNat
    have hsquare : (1 : ℝ) ≤ ((2 * (n + 2) - 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (((2 * (n + 2) - 1 : ℕ) : ℝ)), hn]
    nlinarith
  positivity

lemma bhmtTanOddTail_summable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (fun n : ℕ => bhmtTanOddTail u n) := by
  have hnonneg : ∀ n, 0 ≤ bhmtTanOddTail u n := bhmtTanOddTail_nonneg hu0 hu1
  refine summable_of_sum_range_le (c := 1 / (2 * (1 + u ^ 2))) hnonneg ?_
  intro N
  have hsum_bound :
      (∑ n ∈ Finset.range N, bhmtTanOddTail u n) ≤
        ∑ n ∈ Finset.range N,
          1 / (2 * (1 + u ^ 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact bhmtTanOddTail_term_bound hu0 hu1 n
  have hfactor :
      (∑ n ∈ Finset.range N,
          1 / (2 * (1 + u ^ 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))) =
        (1 / (2 * (1 + u ^ 2))) *
          (∑ n ∈ Finset.range N,
            1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    field_simp [show (2 * (1 + u ^ 2)) ≠ 0 by positivity,
      show ((n + 1 : ℕ) : ℝ) ≠ 0 by positivity,
      show ((n + 2 : ℕ) : ℝ) ≠ 0 by positivity]
  have hpartial_le :
      (∑ n ∈ Finset.range N,
            1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) ≤ 1 := by
    rw [bhmtInvNatSuccMulSuccSucc_sum_telescope]
    have hpos : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
    nlinarith [one_div_pos.mpr hpos]
  calc
    (∑ n ∈ Finset.range N, bhmtTanOddTail u n)
        ≤ ∑ n ∈ Finset.range N,
          1 / (2 * (1 + u ^ 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := hsum_bound
    _ = (1 / (2 * (1 + u ^ 2))) *
          (∑ n ∈ Finset.range N,
            1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) := hfactor
    _ ≤ (1 / (2 * (1 + u ^ 2))) * 1 := by gcongr
    _ = 1 / (2 * (1 + u ^ 2)) := by ring

lemma bhmtTanOddTail_tsum_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑' n : ℕ, bhmtTanOddTail u n) ≤ 1 / (2 * (1 + u ^ 2)) := by
  have hnonneg : ∀ n, 0 ≤ bhmtTanOddTail u n := bhmtTanOddTail_nonneg hu0 hu1
  apply Real.tsum_le_of_sum_range_le hnonneg
  intro N
  have hsum_bound :
      (∑ n ∈ Finset.range N, bhmtTanOddTail u n) ≤
        ∑ n ∈ Finset.range N,
          1 / (2 * (1 + u ^ 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro n hn
    exact bhmtTanOddTail_term_bound hu0 hu1 n
  have hfactor :
      (∑ n ∈ Finset.range N,
          1 / (2 * (1 + u ^ 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ))) =
        (1 / (2 * (1 + u ^ 2))) *
          (∑ n ∈ Finset.range N,
            1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    field_simp [show (2 * (1 + u ^ 2)) ≠ 0 by positivity,
      show ((n + 1 : ℕ) : ℝ) ≠ 0 by positivity,
      show ((n + 2 : ℕ) : ℝ) ≠ 0 by positivity]
  have hpartial_le :
      (∑ n ∈ Finset.range N,
            1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) ≤ 1 := by
    rw [bhmtInvNatSuccMulSuccSucc_sum_telescope]
    have hpos : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
    nlinarith [one_div_pos.mpr hpos]
  have hcoef_nonneg : 0 ≤ (1 / (2 * (1 + u ^ 2)) : ℝ) := by positivity
  calc
    (∑ n ∈ Finset.range N, bhmtTanOddTail u n)
        ≤ ∑ n ∈ Finset.range N,
          1 / (2 * (1 + u ^ 2) * ((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) := hsum_bound
    _ = (1 / (2 * (1 + u ^ 2))) *
          (∑ n ∈ Finset.range N,
            1 / (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ))) := hfactor
    _ ≤ (1 / (2 * (1 + u ^ 2))) * 1 := by gcongr
    _ = 1 / (2 * (1 + u ^ 2)) := by ring

/-- Real cotangent-series term specialized to `z = (1 - u) / 2`. -/
def bhmtRealCotTerm (u : ℝ) (n : ℕ) : ℝ :=
  1 / ((1 - u) / 2 - ((n + 1 : ℕ) : ℝ)) +
    1 / ((1 - u) / 2 + ((n + 1 : ℕ) : ℝ))

/-- Grouped cotangent terms: the positive pole at `n + 1` paired with the next
negative pole at `-(n + 2)`. -/
def bhmtTanGroupedTerm (u : ℝ) (n : ℕ) : ℝ :=
  1 / ((1 - u) / 2 + ((n + 1 : ℕ) : ℝ)) +
    1 / ((1 - u) / 2 - ((n + 2 : ℕ) : ℝ))

lemma bhmtRealCotTerm_summable {z : ℝ}
    (hz : (z : ℂ) ∈ Complex.integerComplement) :
    Summable fun n : ℕ =>
      (1 / (z - ((n + 1 : ℕ) : ℝ)) + 1 / (z + ((n + 1 : ℕ) : ℝ))) := by
  have hs : Summable fun n : ℕ =>
      (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))) := by
    exact summable_cotTerm hz
  have hsre := hs.map Complex.reCLM Complex.reCLM.continuous
  refine hsre.congr ?_
  intro n
  have hcomplex :
      1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1)) =
        ((1 / (z - ((n + 1 : ℕ) : ℝ)) +
          1 / (z + ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
    have hsub : (z : ℂ) - (n + 1) = ((z - ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      norm_num
    have hadd : (z : ℂ) + (n + 1) = ((z + ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      norm_num
    rw [hsub, hadd]
    simp [one_div, Complex.ofReal_inv]
  change (1 / ((z : ℂ) - (n + 1)) + 1 / ((z : ℂ) + (n + 1))).re =
    ((1 / (z - ((n + 1 : ℕ) : ℝ)) +
      1 / (z + ((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ).re
  exact congrArg Complex.re hcomplex

lemma bhmtRealCotTerm_summable_of_bounds {u : ℝ} (_hu0 : 0 ≤ u) (_hu1 : u < 1)
    (hz : (((1 - u) / 2 : ℝ) : ℂ) ∈ Complex.integerComplement) :
    Summable (bhmtRealCotTerm u) := by
  have hs := bhmtRealCotTerm_summable (z := (1 - u) / 2) hz
  refine hs.congr ?_
  intro n
  simp [bhmtRealCotTerm, Nat.cast_add, Nat.cast_one]

lemma bhmtTanGroupedTerm_eq_tail {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (n : ℕ) :
    bhmtTanGroupedTerm u n = 4 * u * bhmtTanOddTail u n := by
  unfold bhmtTanGroupedTerm bhmtTanOddTail
  set m : ℝ := ((2 * (n + 2) - 1 : ℕ) : ℝ)
  have hm_eq : m = 2 * ((n : ℕ) : ℝ) + 3 := by
    have hNat : 2 * (n + 2) - 1 = 2 * n + 3 := by omega
    dsimp [m]
    exact_mod_cast hNat
  have hzp : (1 - u) / 2 + ((n + 1 : ℕ) : ℝ) = (m - u) / 2 := by
    rw [hm_eq]
    norm_num
    ring
  have hzn : (1 - u) / 2 - ((n + 2 : ℕ) : ℝ) = -(m + u) / 2 := by
    rw [hm_eq]
    norm_num
    ring
  have hm_pos : 0 < m := by
    rw [hm_eq]
    positivity
  have hu_lt_m : u < m := by linarith
  have hmpu : m + u ≠ 0 := by nlinarith
  have hmmu : m - u ≠ 0 := by nlinarith
  have hsq : m ^ 2 - u ^ 2 ≠ 0 := by
    have hpos : 0 < m ^ 2 - u ^ 2 := by
      nlinarith [sq_pos_of_pos (sub_pos.mpr hu_lt_m), sq_nonneg (m + u)]
    exact ne_of_gt hpos
  rw [hzp, hzn]
  field_simp [hmpu, hmmu, hsq]
  ring

lemma bhmtTanGroupedTerm_summable {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Summable (bhmtTanGroupedTerm u) := by
  have ht := (bhmtTanOddTail_summable hu0 hu1).mul_left (4 * u)
  refine ht.congr ?_
  intro n
  exact (bhmtTanGroupedTerm_eq_tail hu0 hu1 n).symm

lemma bhmtTanGroupedTerm_tsum {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (∑' n : ℕ, bhmtTanGroupedTerm u n) =
      4 * u * (∑' n : ℕ, bhmtTanOddTail u n) := by
  calc
    (∑' n : ℕ, bhmtTanGroupedTerm u n)
        = ∑' n : ℕ, 4 * u * bhmtTanOddTail u n := by
            apply tsum_congr
            intro n
            exact bhmtTanGroupedTerm_eq_tail hu0 hu1 n
    _ = 4 * u * (∑' n : ℕ, bhmtTanOddTail u n) := by
            exact Summable.tsum_mul_left (4 * u) (bhmtTanOddTail_summable hu0 hu1)

lemma bhmtRealCotTerm_finite_regroup (u : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), bhmtRealCotTerm u k) =
      1 / ((1 - u) / 2 - 1) +
        (∑ n ∈ Finset.range N, bhmtTanGroupedTerm u n) +
        1 / ((1 - u) / 2 + ((N + 1 : ℕ) : ℝ)) := by
  induction N with
  | zero => simp [bhmtRealCotTerm]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      unfold bhmtRealCotTerm bhmtTanGroupedTerm
      ring

lemma bhmtRealCotTerm_endpoint_tendsto_zero (u : ℝ) :
    Tendsto (fun N : ℕ => 1 / ((1 - u) / 2 + ((N + 1 : ℕ) : ℝ))) atTop
      (𝓝 (0 : ℝ)) := by
  have hN : Tendsto (fun N : ℕ => ((1 - u) / 2 + ((N + 1 : ℕ) : ℝ))) atTop atTop := by
    have hcast : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.add_atTop hcast
  simpa [one_div] using hN.inv_tendsto_atTop

lemma bhmtRealCotTerm_tsum_regroup {u : ℝ}
    (hf : Summable (bhmtRealCotTerm u)) (hg : Summable (bhmtTanGroupedTerm u)) :
    (∑' k : ℕ, bhmtRealCotTerm u k) =
      1 / ((1 - u) / 2 - 1) + (∑' n : ℕ, bhmtTanGroupedTerm u n) := by
  have hF : Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), bhmtRealCotTerm u k) atTop
      (𝓝 (∑' k : ℕ, bhmtRealCotTerm u k)) := by
    have h := hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using h
  have hGsum : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, bhmtTanGroupedTerm u n) atTop
      (𝓝 (∑' n : ℕ, bhmtTanGroupedTerm u n)) := hg.hasSum.tendsto_sum_nat
  have hGbase : Tendsto (fun N : ℕ => 1 / ((1 - u) / 2 - 1) +
      (∑ n ∈ Finset.range N, bhmtTanGroupedTerm u n)) atTop
      (𝓝 (1 / ((1 - u) / 2 - 1) + (∑' n : ℕ, bhmtTanGroupedTerm u n))) := by
    exact Filter.Tendsto.const_add _ hGsum
  have hG : Tendsto (fun N : ℕ => 1 / ((1 - u) / 2 - 1) +
      (∑ n ∈ Finset.range N, bhmtTanGroupedTerm u n) +
      1 / ((1 - u) / 2 + ((N + 1 : ℕ) : ℝ))) atTop
      (𝓝 (1 / ((1 - u) / 2 - 1) + (∑' n : ℕ, bhmtTanGroupedTerm u n) + 0)) := by
    exact Filter.Tendsto.add hGbase (bhmtRealCotTerm_endpoint_tendsto_zero u)
  have hF' : Tendsto (fun N : ℕ => 1 / ((1 - u) / 2 - 1) +
      (∑ n ∈ Finset.range N, bhmtTanGroupedTerm u n) +
      1 / ((1 - u) / 2 + ((N + 1 : ℕ) : ℝ))) atTop
      (𝓝 (∑' k : ℕ, bhmtRealCotTerm u k)) := by
    refine Filter.Tendsto.congr' (Eventually.of_forall ?_) hF
    intro N
    exact bhmtRealCotTerm_finite_regroup u N
  have hEq := tendsto_nhds_unique hF' hG
  simpa using hEq

lemma bhmtHalfOneMinus_mem_integerComplement {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (((1 - u) / 2 : ℝ) : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hre : (n : ℝ) = (1 - u) / 2 := by
    have h := congrArg Complex.re hn
    simpa using h
  have hzpos : 0 < (1 - u) / 2 := by linarith
  have hzle : (1 - u) / 2 ≤ 1 / 2 := by nlinarith
  have hn_int_pos : (0 : ℤ) < n := by
    by_contra hnot
    have hnle : n ≤ 0 := le_of_not_gt hnot
    have hnreal : (n : ℝ) ≤ 0 := by exact_mod_cast hnle
    linarith
  have hn_ge_one : (1 : ℤ) ≤ n := by omega
  have hnreal_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hn_ge_one
  nlinarith

lemma bhmtTan_base_poles {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    1 / ((1 - u) / 2) + 1 / ((1 - u) / 2 - 1) = 4 * u / (1 - u ^ 2) := by
  have hminus : (1 - u) / 2 - 1 = -((1 + u) / 2) := by ring
  have h1 : 1 - u ≠ 0 := by linarith
  have h2 : 1 + u ≠ 0 := by nlinarith
  have h3 : 1 - u ^ 2 ≠ 0 := by
    have hpos : 0 < 1 - u ^ 2 := by
      have hu1sq : u ^ 2 < 1 := by
        rw [sq_lt_one_iff_abs_lt_one, abs_of_nonneg hu0]
        exact hu1
      linarith
    exact ne_of_gt hpos
  rw [hminus]
  field_simp [h1, h2, h3]
  ring

/-- The tangent partial-fraction identity used in the BHMT `k = 1` proof,
derived from Mathlib's cotangent Mittag-Leffler expansion by real-part projection
and odd-pole regrouping. -/
theorem bhmtTanPartialFractionIdentity_of_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    bhmtTanPartialFractionIdentity u := by
  have hz := bhmtHalfOneMinus_mem_integerComplement hu0 hu1
  have hcot := real_cot_series_rep' (z := (1 - u) / 2) hz
  have hf := bhmtRealCotTerm_summable_of_bounds hu0 hu1 hz
  have hg := bhmtTanGroupedTerm_summable hu0 hu1
  have hreg := bhmtRealCotTerm_tsum_regroup (u := u) hf hg
  have htail := bhmtTanGroupedTerm_tsum hu0 hu1
  unfold bhmtTanPartialFractionIdentity
  have hcot_tan :
      Real.cot (Real.pi * ((1 - u) / 2)) = Real.tan (Real.pi * u / 2) := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    have harg : Real.pi * ((1 - u) / 2) = Real.pi / 2 - Real.pi * u / 2 := by ring
    rw [harg, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  rw [← hcot_tan]
  have hseries :
      (∑' n : ℕ, (1 / ((1 - u) / 2 - ((n + 1 : ℕ) : ℝ)) +
        1 / ((1 - u) / 2 + ((n + 1 : ℕ) : ℝ)))) =
        1 / ((1 - u) / 2 - 1) + 4 * u * (∑' n : ℕ, bhmtTanOddTail u n) := by
    calc
      (∑' n : ℕ, (1 / ((1 - u) / 2 - ((n + 1 : ℕ) : ℝ)) +
        1 / ((1 - u) / 2 + ((n + 1 : ℕ) : ℝ))))
          = ∑' n : ℕ, bhmtRealCotTerm u n := by
              apply tsum_congr
              intro n
              simp [bhmtRealCotTerm, Nat.cast_add, Nat.cast_one]
      _ = 1 / ((1 - u) / 2 - 1) + (∑' n : ℕ, bhmtTanGroupedTerm u n) := hreg
      _ = 1 / ((1 - u) / 2 - 1) + 4 * u * (∑' n : ℕ, bhmtTanOddTail u n) := by rw [htail]
  rw [hseries] at hcot
  have hmain : Real.pi * Real.cot (Real.pi * ((1 - u) / 2)) =
      1 / ((1 - u) / 2) + 1 / ((1 - u) / 2 - 1) +
        4 * u * (∑' n : ℕ, bhmtTanOddTail u n) := by
    linarith
  rw [hmain]
  rw [bhmtTan_base_poles hu0 hu1]

/-- Reparametrized derivative identity for the two-nearest `k = 1` core.
With `u = 1 - 2x`, the derivative in `x` is a negative factor times the
logarithmic derivative in the tangent-series proof. -/
lemma deriv_bhmtK1TwoNearestCore_eq_neg_log_factor
    {x : ℝ} (hx0p : 0 < x) (hxhalf : x < 1 / 2) :
    deriv bhmtK1TwoNearestCore x =
      -2 * (8 * (1 + (1 - 2 * x) ^ 2) *
          Real.cos (Real.pi * (1 - 2 * x) / 2) ^ 2 /
          (1 - (1 - 2 * x) ^ 2) ^ 2) *
        (2 * (1 - 2 * x) / (1 + (1 - 2 * x) ^ 2) +
          4 * (1 - 2 * x) / (1 - (1 - 2 * x) ^ 2) -
          Real.pi * Real.tan (Real.pi * (1 - 2 * x) / 2)) := by
  have hx0 : x ≠ 0 := ne_of_gt hx0p
  have hx1 : 1 - x ≠ 0 := by linarith
  rw [deriv_bhmtK1TwoNearestCore hx0 hx1]
  have hsin : Real.sin (Real.pi * x) = Real.cos (Real.pi * (1 - 2 * x) / 2) := by
    have harg : Real.pi * x = Real.pi / 2 - Real.pi * (1 - 2 * x) / 2 := by ring
    rw [harg, Real.sin_pi_div_two_sub]
  have hcos : Real.cos (Real.pi * x) = Real.sin (Real.pi * (1 - 2 * x) / 2) := by
    have harg : Real.pi * x = Real.pi / 2 - Real.pi * (1 - 2 * x) / 2 := by ring
    rw [harg, Real.cos_pi_div_two_sub]
  rw [hsin, hcos]
  rw [Real.tan_eq_sin_div_cos]
  have hcospos : 0 < Real.cos (Real.pi * (1 - 2 * x) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos, hx0p, hxhalf]
    · have hu_lt_one : 1 - 2 * x < 1 := by linarith
      nlinarith [Real.pi_pos, hu_lt_one]
  have hdenA : 1 + (1 - 2 * x) ^ 2 ≠ 0 := by positivity
  have hdenB : 1 - (1 - 2 * x) ^ 2 ≠ 0 := by
    have h : 0 < 1 - (1 - 2 * x) ^ 2 := by nlinarith [hx0p, hxhalf]
    positivity
  field_simp [hx0, hx1, hdenA, hdenB, hcospos.ne']
  ring_nf

lemma bhmt_log_derivative_expr_nonneg_of_tan_series
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (htan : bhmtTanPartialFractionIdentity u) :
    0 ≤ 2 * u / (1 + u ^ 2) + 4 * u / (1 - u ^ 2) -
      Real.pi * Real.tan (Real.pi * u / 2) := by
  have htail := bhmtTanOddTail_tsum_le hu0 hu1
  have hmul : 4 * u * (∑' n : ℕ, bhmtTanOddTail u n) ≤
      4 * u * (1 / (2 * (1 + u ^ 2))) := by
    exact mul_le_mul_of_nonneg_left htail (by positivity)
  have hmul' : 4 * u * (∑' n : ℕ, bhmtTanOddTail u n) ≤ 2 * u / (1 + u ^ 2) := by
    calc
      4 * u * (∑' n : ℕ, bhmtTanOddTail u n)
          ≤ 4 * u * (1 / (2 * (1 + u ^ 2))) := hmul
      _ = 2 * u / (1 + u ^ 2) := by
          field_simp [show (1 + u ^ 2) ≠ 0 by positivity]
          ring
  have hnonneg : 0 ≤ 2 * u / (1 + u ^ 2) - 4 * u * (∑' n : ℕ, bhmtTanOddTail u n) := by
    exact sub_nonneg.mpr hmul'
  rw [htan]
  ring_nf
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hnonneg

/-- Unconditional derivative sign for the BHMT `k = 1` two-nearest core. -/
theorem bhmtK1TwoNearestCore_deriv_nonpos :
    ∀ x ∈ Set.Ioo (0 : ℝ) (1 / 2), deriv bhmtK1TwoNearestCore x ≤ 0 := by
  intro x hx
  have hx0 : 0 < x := hx.1
  have hxhalf : x < 1 / 2 := hx.2
  set u : ℝ := 1 - 2 * x
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u < 1 := by dsimp [u]; linarith
  have htan : bhmtTanPartialFractionIdentity u :=
    bhmtTanPartialFractionIdentity_of_bounds hu0 hu1
  have hlog := bhmt_log_derivative_expr_nonneg_of_tan_series hu0 hu1 htan
  have hderiv := deriv_bhmtK1TwoNearestCore_eq_neg_log_factor hx0 hxhalf
  have hfactor_nonneg :
      0 ≤ 8 * (1 + u ^ 2) * Real.cos (Real.pi * u / 2) ^ 2 / (1 - u ^ 2) ^ 2 := by
    positivity
  have hneg_factor :
      -2 * (8 * (1 + u ^ 2) * Real.cos (Real.pi * u / 2) ^ 2 / (1 - u ^ 2) ^ 2) ≤ 0 := by
    nlinarith
  have hprod :
      -2 * (8 * (1 + u ^ 2) * Real.cos (Real.pi * u / 2) ^ 2 / (1 - u ^ 2) ^ 2) *
        (2 * u / (1 + u ^ 2) + 4 * u / (1 - u ^ 2) - Real.pi * Real.tan (Real.pi * u / 2)) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg hneg_factor hlog
  rw [hderiv]
  simpa [u] using hprod

/-- Unconditional `k = 1` two-nearest geometric lower bound, using the proved
left-half monotonicity of the core real function. -/
theorem qpeApproxGeometricProbability_two_nearest_lower_bound_k1_of_core_antitone_left
    {N : ℕ} {x : ℝ} (hN : 0 < N) (hx0 : 0 < x) (hx1 : x < 1) :
    8 / Real.pi ^ 2 ≤
      qpeApproxGeometricProbability N (x / (N : ℝ)) +
        qpeApproxGeometricProbability N (-(1 - x) / (N : ℝ)) := by
  have hanti : AntitoneOn bhmtK1TwoNearestCore (Set.Ioc (0 : ℝ) (1 / 2)) :=
    bhmtK1TwoNearestCore_antitone_left_of_deriv_nonpos bhmtK1TwoNearestCore_deriv_nonpos
  have hcore := qpeApproxGeometricProbability_two_nearest_lower_bound_of_core (N := N) hN hx0 hx1
  have h8 := bhmtK1TwoNearestCore_ge_eight_of_antitone_left hanti hx0 hx1
  have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
  exact le_trans (div_le_div_of_nonneg_right h8 hpi_sq_pos.le) hcore

/-- `k = 1` circular-window lower bound from two explicitly identified adjacent
outcomes, using the proved two-nearest geometric estimate. -/
theorem qpeCircularPhaseWindowProbability_lower_bound_k1_of_two_adjacent_geometric
    (m : ℕ) {theta x : ℝ} (y₀ y₁ : Fin (M m))
    (hx₀ : 0 < x) (hx₁ : x < 1)
    (hy₀win : y₀ ∈ qpeCircularPhaseWindowOutcomes m 1 theta)
    (hy₁win : y₁ ∈ qpeCircularPhaseWindowOutcomes m 1 theta)
    (hy₀₁ : y₀ ≠ y₁)
    (hprob₀ : qpeApproxOutcomeProbability m theta y₀ =
      qpeApproxGeometricProbability (M m) (x / (M m : ℝ)))
    (hprob₁ : qpeApproxOutcomeProbability m theta y₁ =
      qpeApproxGeometricProbability (M m) (-(1 - x) / (M m : ℝ))) :
    8 / Real.pi ^ 2 ≤ qpeCircularPhaseWindowProbability m 1 theta := by
  have hgeom := qpeApproxGeometricProbability_two_nearest_lower_bound_k1_of_core_antitone_left
    (N := M m) (x := x) (Nat.two_pow_pos m) hx₀ hx₁
  apply qpeCircularPhaseWindowProbability_lower_bound_two_outcomes
    (m := m) (k := 1) (theta := theta) (y₀ := y₀) (y₁ := y₁)
    hy₀win hy₁win hy₀₁
  simpa [hprob₀, hprob₁] using hgeom

/-- Unconditional BHMT11 `k = 1` circular-window probability bound. -/
theorem qpeCircularPhaseWindowProbability_lower_bound_k1
    (m : ℕ) {theta : ℝ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1) :
    bhmt11SuccessProbability 1 ≤ qpeCircularPhaseWindowProbability m 1 theta := by
  rw [bhmt11SuccessProbability, if_pos rfl]
  by_cases hm0 : m = 0
  · subst m
    let y := zeroIndex 0
    have hprob_one : qpeApproxOutcomeProbability 0 theta y = 1 := by
      unfold qpeApproxOutcomeProbability
      rw [qpeApproxAmplitude_eq_normalized_phase_sum]
      simp [M, y, zeroIndex]
    have hywin : y ∈ qpeCircularPhaseWindowOutcomes 0 1 theta := by
      apply (mem_qpeCircularPhaseWindowOutcomes_iff 0 1 theta y).mpr
      unfold qpeCircularPhaseWindow
      have hdist : unitPhaseDistance theta (((y : ℕ) : ℝ) / (M 0 : ℝ)) ≤ 1 := by
        exact le_trans (unitPhaseDistance_le_abs_sub theta (((y : ℕ) : ℝ) / (M 0 : ℝ))) (by
          dsimp [y, zeroIndex, M]
          simpa [abs_of_nonneg h0] using h1)
      simpa [M] using hdist
    unfold qpeCircularPhaseWindowProbability
    have hsingle : qpeApproxOutcomeProbability 0 theta y ≤
        (qpeCircularPhaseWindowOutcomes 0 1 theta).sum
          (fun z => qpeApproxOutcomeProbability 0 theta z) :=
      Finset.single_le_sum (fun z _hz => qpeApproxOutcomeProbability_nonneg 0 theta z) hywin
    rw [hprob_one] at hsingle
    have h8_le_one : 8 / Real.pi ^ 2 ≤ 1 := by
      have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
      have hpi_sq_ge_eight : 8 ≤ Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_three]
      exact (div_le_one hpi_sq_pos).mpr hpi_sq_ge_eight
    exact le_trans h8_le_one hsingle
  by_cases htheta1 : theta = 1
  · subst theta
    let y := zeroIndex m
    have hprob_zero : qpeApproxOutcomeProbability m 0 y = 1 := by
      have hclose : |(0 : ℝ) - (((y : ℕ) : ℝ) / (M m : ℝ))| ≤
          1 / (2 * (M m : ℝ)) := by
        dsimp [y, zeroIndex]
        simp
      have hgeom := qpeApproxOutcomeProbability_eq_geometric_of_nearest m 0 y hclose
      rw [hgeom]
      simp [qpeApproxGeometricProbability, y, zeroIndex]
    have hprob_one : qpeApproxOutcomeProbability m 1 y = 1 := by
      have hperiod : qpeApproxOutcomeProbability m 1 y = qpeApproxOutcomeProbability m (1 - 1) y := by
        have h := qpeApproxOutcomeProbability_add_one m (1 - 1) y
        have harg : (1 : ℝ) - 1 + 1 = 1 := by ring_nf
        simpa [harg] using h
      rw [hperiod]
      simpa using hprob_zero
    have hywin : y ∈ qpeCircularPhaseWindowOutcomes m 1 1 := by
      apply (mem_qpeCircularPhaseWindowOutcomes_iff m 1 1 y).mpr
      unfold qpeCircularPhaseWindow unitPhaseDistance
      dsimp [y, zeroIndex]
      simp
    unfold qpeCircularPhaseWindowProbability
    have hsingle : qpeApproxOutcomeProbability m 1 y ≤
        (qpeCircularPhaseWindowOutcomes m 1 1).sum
          (fun z => qpeApproxOutcomeProbability m 1 z) :=
      Finset.single_le_sum (fun z _hz => qpeApproxOutcomeProbability_nonneg m 1 z) hywin
    rw [hprob_one] at hsingle
    have h8_le_one : 8 / Real.pi ^ 2 ≤ 1 := by
      have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero Real.pi_ne_zero
      have hpi_sq_ge_eight : 8 ≤ Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_three]
      exact (div_le_one hpi_sq_pos).mpr hpi_sq_ge_eight
    exact le_trans h8_le_one hsingle
  have htheta_lt : theta < 1 := lt_of_le_of_ne h1 htheta1
  by_cases hxzero : qpeFractionalOffset m theta = 0
  · exact qpeCircularPhaseWindowProbability_lower_bound_k1_exactGrid_of_mem_Ico
      m h0 htheta_lt hxzero
  · have hxpos : 0 < qpeFractionalOffset m theta :=
      lt_of_le_of_ne (Int.fract_nonneg ((M m : ℝ) * theta)) (Ne.symm hxzero)
    have hxlt : qpeFractionalOffset m theta < 1 :=
      Int.fract_lt_one ((M m : ℝ) * theta)
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    exact qpeCircularPhaseWindowProbability_lower_bound_k1_of_two_adjacent_geometric
      (m := m) (theta := theta) (x := qpeFractionalOffset m theta)
      (y₀ := qpeLowerAdjacentOutcome m theta) (y₁ := qpeUpperAdjacentOutcome m theta)
      hxpos hxlt
      (qpeLowerAdjacentOutcome_mem_circularWindow_one_of_mem_Ico m h0 htheta_lt)
      (qpeUpperAdjacentOutcome_mem_circularWindow_one_of_mem_Ico m h0 htheta_lt)
      (qpeAdjacentOutcomes_ne_of_pos_m m hmpos h0 htheta_lt)
      (qpeApproxOutcomeProbability_lowerAdjacent_eq_geometric_fractionalOffset
        m h0 htheta_lt hxpos)
      (qpeApproxOutcomeProbability_upperAdjacent_eq_geometric_fractionalOffset
        m h0 htheta_lt hxpos)

/-- BHMT11 circular-window probability bound, combining the proved `k = 1` and
`k > 1` branches. -/
theorem bhmt11CircularWindowBound_proved : BHMT11CircularWindowBound := by
  intro m k theta h0 h1 hk
  by_cases hk1 : k = 1
  · subst k
    exact qpeCircularPhaseWindowProbability_lower_bound_k1 m h0 h1
  · have hkgt : 1 < k := by omega
    exact qpeCircularPhaseWindowProbability_lower_bound_k_gt_one m k h0 h1 hkgt

end QPE
end QAE
