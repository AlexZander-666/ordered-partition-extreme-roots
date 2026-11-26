import OrderedPartitions.ReciprocalEdgeFirstCorrectionCoefficient
import Mathlib.Algebra.Field.GeomSum

/-! Exact low coefficients and geometric coefficient bounds for the reciprocal series. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Finset PowerSeries

private theorem unmarked_coeff {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    coeff m (A j) = if 1 ≤ m ∧ m < j then (m.factorial:ℝ)⁻¹ else 0 := by
  rw [A, map_sub]
  by_cases pos : 1 ≤ m
  · by_cases large : j ≤ m
    · simp [sizeSeries, pos, large, not_lt_of_ge large]
    · simp [sizeSeries, pos, large, lt_of_not_ge large]
  · simp [sizeSeries, pos, show ¬j≤m by omega]

private theorem unmarked_bounds {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    0 ≤ coeff m (A j) ∧ coeff m (A j) ≤ 1 := by
  rw [unmarked_coeff hj]
  split_ifs
  · exact ⟨by positivity, inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos m)⟩
  · norm_num

private theorem unmarked_sequence_step {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    coeff (m+1) (V j) = ∑ i ∈ range (m+1), coeff (i+1) (A j) * coeff (m-i) (V j) := by
  have az : constantCoeff (A j) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, unmarked_coeff hj]
    simp
  have inverse : (1-A j)*V j = 1 := PowerSeries.mul_inv_cancel _ (by simp [az])
  rw [sub_mul, one_mul] at inverse
  conv_lhs => rw [sub_eq_iff_eq_add.mp inverse]
  rw [map_add, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
  simp [PowerSeries.coeff_one, coeff_zero_eq_constantCoeff_apply, az, Nat.succ_sub_succ_eq_sub]

theorem V_two {j : ℕ} (hj : 2 ≤ j) :
    coeff 2 (V j) = 1+(if j=2 then 0 else (1/2:ℝ)) := by
  rw [unmarked_sequence_step hj 1, sum_range_succ, sum_range_one]
  have h1 : 1 < j := by omega
  simp only [unmarked_coeff hj, V_zero hj, V_one hj, Nat.zero_add, Nat.sub_zero,
    Nat.sub_self, Nat.factorial_one, Nat.cast_one, inv_one, mul_one]
  by_cases j2 : j=2
  · simp [j2]
  · norm_num [j2, h1, show 2 < j by omega]

private theorem U_two (j : ℕ) :
    coeff 2 (U j) = 1/(((j:ℝ)+1)*((j:ℝ)+2)) := by
  rw [U, coeff_mk, show j+2=(j+1)+1 by omega, Nat.factorial_succ,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
  push_cast
  field_simp
  ring

/-- The quadratic coefficient includes one unmarked two-block exactly when j > 2. -/
theorem H_two {j : ℕ} (hj : 2 ≤ j) :
    coeff 2 (H j) =
      1+(if j=2 then 0 else (1/2:ℝ)) + 1/((j:ℝ)+1)+1/(((j:ℝ)+1)*((j:ℝ)+2)) := by
  rw [H, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [sum_range_succ, V_zero hj, V_one hj, V_two hj, U_zero, U_one, U_two]

theorem V_first_correction_bounds {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    0 ≤ coeff m (V j) ∧ coeff m (V j) ≤ (2:ℝ)^m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp [V_zero hj]
    | succ m =>
      rw [unmarked_sequence_step hj]
      have earlier (i : ℕ) := ih (m-i) (by omega : m-i < m+1)
      refine ⟨sum_nonneg (fun i _ ↦ mul_nonneg (unmarked_bounds hj (i+1)).1 (earlier i).1), ?_⟩
      calc
        _ ≤ ∑ i ∈ range (m+1), (2:ℝ)^(m-i) := sum_le_sum fun i _ ↦ by
          simpa only [one_mul] using mul_le_mul (unmarked_bounds hj (i+1)).2 (earlier i).2
            (earlier i).1 (by norm_num : (0:ℝ)≤1)
        _ = ∑ i ∈ range (m+1), (2:ℝ)^i := sum_range_reflect (fun i ↦ (2:ℝ)^i) (m+1)
        _ ≤ (2:ℝ)^(m+1) := by rw [geom_sum_eq (by norm_num : (2:ℝ)≠1)]; norm_num

private theorem U_bounds (j m : ℕ) : 0 ≤ coeff m (U j) ∧ coeff m (U j) ≤ 1 := by
  rw [U, coeff_mk]
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right j m))⟩

theorem H_first_correction_bounds {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    0 ≤ coeff m (H j) ∧ coeff m (H j) ≤ (4:ℝ)^m := by
  have length_cap : ((m:ℝ)+1) ≤ (2:ℝ)^m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Nat.cast_succ, pow_succ]
      linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [H, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine ⟨sum_nonneg (fun i _ ↦ mul_nonneg (U_bounds j i).1
      (V_first_correction_bounds hj (m-i)).1), ?_⟩
  calc
    _ ≤ ∑ _i ∈ range (m+1), (2:ℝ)^m := sum_le_sum fun i _ ↦ by
      have v := V_first_correction_bounds hj (m-i)
      have bound := v.2.trans (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.sub_le m i))
      simpa only [one_mul] using mul_le_mul (U_bounds j i).2 bound v.1 (by norm_num : (0:ℝ)≤1)
    _ = ((m:ℝ)+1)*(2:ℝ)^m := by simp
    _ ≤ (2:ℝ)^m*(2:ℝ)^m := mul_le_mul_of_nonneg_right length_cap (by positivity)
    _ = (4:ℝ)^m := by rw [← mul_pow]; norm_num

#print axioms H_two
#print axioms V_first_correction_bounds
#print axioms H_first_correction_bounds

end OrderedPartitions.ReciprocalEdge
