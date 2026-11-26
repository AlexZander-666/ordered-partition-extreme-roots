import OrderedPartitions.MarkedSeries
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Ordinary coefficient slices for the original labeled ordered-partition rows. -/

noncomputable section
open Finset PowerSeries

namespace OrderedPartitions.ReciprocalEdge

/-- The EGF for one unmarked block. -/
def A (j : ℕ) : PowerSeries ℝ := sizeSeries 1 - sizeSeries j

/-- The EGF for an ordered list of unmarked blocks. -/
def V (j : ℕ) : PowerSeries ℝ := (1 - A j)⁻¹

/-- The EGF for a marked block after removing its initial monomial. -/
def U (j : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun m ↦ (j.factorial : ℝ) / (j + m).factorial

/-- A normalized marked block followed by an unmarked list. -/
def H (j : ℕ) : PowerSeries ℝ := U j * V j

private def ordinarySeries (j k : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun n ↦ (row n j).coeff k / n.factorial

private theorem coeff_A {j : ℕ} (hj : 1 ≤ j) (r : ℕ) :
    coeff r (A j) = if 1 ≤ r ∧ r < j then (r.factorial : ℝ)⁻¹ else 0 := by
  rw [A, map_sub]
  by_cases small : 1 ≤ r
  · by_cases large : j ≤ r
    · simp [sizeSeries, small, large, not_lt_of_ge large]
    · simp [sizeSeries, small, large, lt_of_not_ge large]
  · simp [sizeSeries, small, show ¬ j ≤ r from fun h ↦ small (hj.trans h)]

private theorem unmarked_constant {j : ℕ} (hj : 1 ≤ j) : constantCoeff (A j) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_A hj]
  simp

private theorem marked_constant {j : ℕ} (hj : 1 ≤ j) : coeff 0 (sizeSeries j) = 0 := by
  simp [sizeSeries, show ¬ j ≤ 0 by omega]

private theorem convolution {P Q : PowerSeries ℝ} (constant : coeff 0 P = 0) (n : ℕ) :
    coeff n (P * Q) = ∑ r ∈ Icc 1 n, coeff r P * coeff (n-r) Q := by
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  apply sum_subset
  · intro r hr
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hr).2)
  · intro r hr outside
    have bound := Nat.le_of_lt_succ (mem_range.mp hr)
    have zero : r = 0 := by
      by_contra h
      exact outside (mem_Icc.mpr ⟨by omega, bound⟩)
    simp [zero, constant]

private theorem normalized_recurrence (n k : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    coeff (n+1) (ordinarySeries j k) = coeff (n+1) (A j * ordinarySeries j k) +
      if k = 0 then 0 else coeff (n+1) (sizeSeries j * ordinarySeries j (k-1)) := by
  have az : coeff 0 (A j) = 0 := by rw [coeff_zero_eq_constantCoeff_apply, unmarked_constant hj]
  rw [convolution az, convolution (marked_constant hj)]
  simp only [ordinarySeries, PowerSeries.coeff_mk, coeff_row hj]
  rw [count_recurrence n hj, Nat.cast_sum, sum_div]
  cases k with
  | zero =>
    simp only [ite_true, add_zero]
    apply sum_congr rfl
    intro r hr
    have hr1 := (mem_Icc.mp hr).1
    rw [Nat.cast_mul, Nat.cast_choose ℝ (mem_Icc.mp hr).2, coeff_A hj]
    by_cases big : j ≤ r
    · simp [big, not_lt_of_ge big]
    · simp [big, hr1, lt_of_not_ge big]
      field_simp
  | succ k =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro r hr
    have hr1 := (mem_Icc.mp hr).1
    rw [Nat.cast_mul, Nat.cast_choose ℝ (mem_Icc.mp hr).2, coeff_A hj]
    by_cases big : j ≤ r
    · simp [sizeSeries, big, not_lt_of_ge big]
      field_simp
    · simp [sizeSeries, big, hr1, lt_of_not_ge big]
      field_simp

private theorem ordinary_zero_rank {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    coeff 0 (ordinarySeries j k) = if k = 0 then 1 else 0 := by
  simp [ordinarySeries, row_zero hj, Polynomial.coeff_one]

private theorem ordinary_zero_resolvent {j : ℕ} (hj : 1 ≤ j) :
    (1-A j) * ordinarySeries j 0 = 1 := by
  rw [sub_mul, one_mul]
  ext n
  rw [map_sub]
  cases n with
  | zero =>
    simp [ordinary_zero_rank hj, coeff_zero_eq_constantCoeff_apply, unmarked_constant hj]
  | succ n =>
    have step := normalized_recurrence n 0 hj
    simpa [PowerSeries.coeff_one] using sub_eq_zero.mpr (by simpa using step)

private theorem ordinary_succ_resolvent {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    (1-A j) * ordinarySeries j (k+1) = sizeSeries j * ordinarySeries j k := by
  rw [sub_mul, one_mul]
  ext n
  rw [map_sub]
  cases n with
  | zero =>
    have bz := marked_constant hj
    rw [coeff_zero_eq_constantCoeff_apply] at bz
    simp [ordinary_zero_rank hj, coeff_zero_eq_constantCoeff_apply,
      unmarked_constant hj, bz]
  | succ n =>
    have step := normalized_recurrence n (k+1) hj
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using step)

private theorem V_resolvent {j : ℕ} (hj : 1 ≤ j) : (1-A j) * V j = 1 := by
  exact PowerSeries.mul_inv_cancel _ (by simp [unmarked_constant hj])

private theorem ordinary_series {j : ℕ} (hj : 1 ≤ j) (k : ℕ) :
    ordinarySeries j k = sizeSeries j ^ k * V j ^ (k+1) := by
  induction k with
  | zero =>
    calc
      ordinarySeries j 0 = V j * ((1-A j) * ordinarySeries j 0) := by
        rw [← mul_assoc, mul_comm (V j), V_resolvent hj, one_mul]
      _ = sizeSeries j ^ 0 * V j ^ (0+1) := by rw [ordinary_zero_resolvent hj]; simp
  | succ k ih =>
    calc
      ordinarySeries j (k+1) = V j * ((1-A j) * ordinarySeries j (k+1)) := by
        rw [← mul_assoc, mul_comm (V j), V_resolvent hj, one_mul]
      _ = sizeSeries j ^ (k+1) * V j ^ (k+1+1) := by
        rw [ordinary_succ_resolvent hj, ih, pow_succ (sizeSeries j), pow_succ (V j) (k+1)]
        ring

/-- The EGF of the ordinary coefficient of the true ordered-partition row. -/
theorem ordinary_coefficient {j : ℕ} (hj : 2 ≤ j) (n k : ℕ) :
    (row n j).coeff k / (n.factorial : ℝ) = coeff n (sizeSeries j ^ k * V j ^ (k+1)) := by
  simpa [ordinarySeries] using congrArg (fun S ↦ coeff n S) (ordinary_series (by omega) k)

/-- Restoring the lowest-rank monomial and its factorial recovers the large-block EGF. -/
theorem sizeSeries_eq_shift (j : ℕ) :
    sizeSeries j = C ((j.factorial : ℝ)⁻¹) * (U j * X ^ j) := by
  ext n
  rw [coeff_C_mul, coeff_mul_X_pow']
  by_cases bound : j ≤ n
  · have index : j + (n-j) = n := Nat.add_sub_of_le bound
    simp [sizeSeries, U, bound, index]
    field_simp
  · simp [sizeSeries, bound]

/-- The original coefficient at a fixed rank offset from the minimal rank for `k` blocks. -/
theorem coefficient_at_offset {j : ℕ} (hj : 2 ≤ j) (k m : ℕ) :
    (row (k*j+m) j).coeff k / ((k*j+m).factorial : ℝ) =
      ((j.factorial : ℝ)⁻¹)^k * coeff m (V j * H j ^ k) := by
  have rearrange : sizeSeries j ^ k * V j ^ (k+1) =
      C (((j.factorial : ℝ)⁻¹)^k) * ((V j * H j ^ k) * X^(k*j)) := by
    rw [sizeSeries_eq_shift, mul_pow, mul_pow, ← map_pow, ← pow_mul, Nat.mul_comm j k,
      H, mul_pow, pow_succ (V j)]
    ring
  rw [ordinary_coefficient hj, rearrange, coeff_C_mul, Nat.add_comm (k*j) m, coeff_mul_X_pow]

/-- The leading-edge coefficient with rank written as `j*d+r` and degree as `d-h`. -/
theorem edge_coefficient {j : ℕ} (hj : 2 ≤ j) (d r h : ℕ) (hle : h ≤ d) :
    (row (j*d+r) j).coeff (d-h) / ((j*d+r).factorial : ℝ) =
      ((j.factorial : ℝ)⁻¹)^(d-h) * coeff (r+j*h) (V j * H j ^ (d-h)) := by
  have index : (d-h)*j+(r+j*h) = j*d+r := by
    calc
      _ = j*(d-h+h)+r := by ring
      _ = _ := by rw [Nat.sub_add_cancel hle]
  simpa only [index] using coefficient_at_offset hj (d-h) (r+j*h)

theorem V_zero {j : ℕ} (hj : 2 ≤ j) : coeff 0 (V j) = 1 := by
  rw [V, coeff_zero_eq_constantCoeff_apply, constantCoeff_inv, map_sub, map_one,
    unmarked_constant (by omega : 1 ≤ j), sub_zero, inv_one]

theorem V_one {j : ℕ} (hj : 2 ≤ j) : coeff 1 (V j) = 1 := by
  have admissible : 1 ≤ j := by omega
  have identity := congrArg (fun S ↦ coeff 1 S) (V_resolvent admissible)
  have az := unmarked_constant admissible
  have ao : coeff 1 (A j) = 1 := by simp [coeff_A admissible, show 1 < j by omega]
  have vz : constantCoeff (V j) = 1 := by rw [← coeff_zero_eq_constantCoeff_apply, V_zero hj]
  rw [sub_mul, one_mul, map_sub, coeff_one_mul, az, ao, vz] at identity
  simpa [PowerSeries.coeff_one] using sub_eq_zero.mp (by simpa [PowerSeries.coeff_one] using identity)

theorem U_zero (j : ℕ) : coeff 0 (U j) = 1 := by
  simp [U, show (j.factorial : ℝ) ≠ 0 by positivity]

theorem U_one (j : ℕ) : coeff 1 (U j) = (1 : ℝ) / ((j : ℝ)+1) := by
  rw [U, coeff_mk, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  field_simp

theorem H_zero {j : ℕ} (hj : 2 ≤ j) : coeff 0 (H j) = 1 := by
  rw [H, coeff_zero_eq_constantCoeff_apply, map_mul, ← coeff_zero_eq_constantCoeff_apply (U j),
    ← coeff_zero_eq_constantCoeff_apply (V j), U_zero, V_zero hj, one_mul]

theorem H_one {j : ℕ} (hj : 2 ≤ j) : coeff 1 (H j) = 1 + (1 : ℝ) / ((j : ℝ)+1) := by
  rw [H, coeff_one_mul, ← coeff_zero_eq_constantCoeff_apply (U j),
    ← coeff_zero_eq_constantCoeff_apply (V j), U_zero, V_zero hj, U_one, V_one hj]
  ring

/-- Removing the constant and one power of `X` from the normalized series. -/
def L (j : ℕ) : PowerSeries ℝ := PowerSeries.mk fun m ↦ coeff (m+1) (H j)

theorem H_eq_one_add_X_mul {j : ℕ} (hj : 2 ≤ j) : H j = 1 + X * L j := by
  ext n
  cases n with
  | zero => simp [H_zero hj]
  | succ n => simp [L, PowerSeries.coeff_one]

theorem L_zero {j : ℕ} (hj : 2 ≤ j) : coeff 0 (L j) = 1 + (1 : ℝ) / ((j : ℝ)+1) := by
  simpa [L] using H_one hj

#print axioms ordinary_coefficient
#print axioms sizeSeries_eq_shift
#print axioms coefficient_at_offset
#print axioms edge_coefficient
#print axioms V_zero
#print axioms V_one
#print axioms U_zero
#print axioms U_one
#print axioms H_zero
#print axioms H_one
#print axioms H_eq_one_add_X_mul
#print axioms L_zero

end OrderedPartitions.ReciprocalEdge
