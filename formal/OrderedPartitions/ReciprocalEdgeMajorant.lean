import OrderedPartitions.ReciprocalEdgeRowLimit
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Field.GeomSum

/-! A factorial bound uniform in the rank and every degree of the reciprocal row. -/

noncomputable section
open PowerSeries Finset

namespace OrderedPartitions.ReciprocalEdge

private theorem small_caps {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    0 ≤ coeff m (A j) ∧ coeff m (A j) ≤ 1 := by
  rw [A, map_sub]
  by_cases positive : 1 ≤ m
  · by_cases marked : j ≤ m
    · simp [sizeSeries, positive, marked]
    · have fact : 1 ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
      simpa [sizeSeries, positive, marked] using
        And.intro (inv_nonneg.mpr (show 0 ≤ (m.factorial : ℝ) by positivity))
          (inv_le_one_of_one_le₀ fact)
  · simp [sizeSeries, positive, show ¬j ≤ m by omega]

private theorem V_step {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    coeff (m+1) (V j) = ∑ i ∈ range (m+1), coeff (i+1) (A j) * coeff (m-i) (V j) := by
  have az : constantCoeff (A j) = 0 := by
    simp [A, sizeSeries, show ¬j ≤ 0 by omega]
  have inverse : (1-A j) * V j = 1 := PowerSeries.mul_inv_cancel _ (by simp [az])
  rw [sub_mul, one_mul] at inverse
  conv_lhs => rw [sub_eq_iff_eq_add.mp inverse]
  rw [map_add, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
  simp [PowerSeries.coeff_one, coeff_zero_eq_constantCoeff_apply, az, Nat.succ_sub_succ_eq_sub]

private theorem V_caps {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    0 ≤ coeff m (V j) ∧ coeff m (V j) ≤ (2 : ℝ)^m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simp [V_zero hj]
    | succ m =>
      rw [V_step hj]
      have earlier (i : ℕ) := ih (m-i) (by omega : m-i < m+1)
      refine ⟨sum_nonneg (fun i _ ↦ mul_nonneg (small_caps hj (i+1)).1 (earlier i).1), ?_⟩
      calc
        _ ≤ ∑ i ∈ range (m+1), (2 : ℝ)^(m-i) := sum_le_sum fun i _ ↦ by
          have cap := mul_le_mul (small_caps hj (i+1)).2 (earlier i).2
            (earlier i).1 (by norm_num : (0 : ℝ) ≤ 1)
          simpa using cap
        _ = ∑ i ∈ range (m+1), (2 : ℝ)^i := by
          exact sum_range_reflect (fun i ↦ (2 : ℝ)^i) (m+1)
        _ ≤ (2 : ℝ)^(m+1) := by rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; norm_num

private theorem U_caps (j m : ℕ) : 0 ≤ coeff m (U j) ∧ coeff m (U j) ≤ 1 := by
  rw [U, coeff_mk]
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (by
    exact_mod_cast Nat.factorial_le (Nat.le_add_right j m))⟩

private theorem H_caps {j : ℕ} (hj : 2 ≤ j) (m : ℕ) :
    0 ≤ coeff m (H j) ∧ coeff m (H j) ≤ (4 : ℝ)^m := by
  have length_cap : ((m : ℝ)+1) ≤ (2 : ℝ)^m := by
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Nat.cast_succ, pow_succ]
      linarith [Nat.cast_nonneg (α := ℝ) m]
  rw [H, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine ⟨sum_nonneg (fun i _ ↦ mul_nonneg (U_caps j i).1 (V_caps hj (m-i)).1), ?_⟩
  calc
    _ ≤ ∑ _i ∈ range (m+1), (2 : ℝ)^m := sum_le_sum fun i _ ↦ by
      have right := (V_caps hj (m-i)).2.trans
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le m i))
      simpa using mul_le_mul (U_caps j i).2 right (V_caps hj (m-i)).1 (by norm_num : (0 : ℝ) ≤ 1)
    _ = ((m : ℝ)+1)*(2 : ℝ)^m := by simp
    _ ≤ (2 : ℝ)^m * (2 : ℝ)^m := mul_le_mul_of_nonneg_right length_cap (by positivity)
    _ = (4 : ℝ)^m := by rw [← mul_pow]; norm_num

private def coefficientBound (f g : PowerSeries ℝ) : Prop :=
  ∀ m, 0 ≤ coeff m f ∧ coeff m f ≤ coeff m g

private theorem coefficientBound.mul {f g p q : PowerSeries ℝ}
    (fg : coefficientBound f g) (pq : coefficientBound p q) : coefficientBound (f*p) (g*q) := by
  intro m
  simp only [coeff_mul]
  refine ⟨sum_nonneg (fun i _ ↦ mul_nonneg (fg i.1).1 (pq i.2).1), ?_⟩
  exact sum_le_sum fun i _ ↦ mul_le_mul (fg i.1).2 (pq i.2).2 (pq i.2).1 ((fg i.1).1.trans (fg i.1).2)

private theorem coefficientBound.pow {f g : PowerSeries ℝ}
    (fg : coefficientBound f g) (d : ℕ) : coefficientBound (f^d) (g^d) := by
  induction d with
  | zero => intro m; cases m <;> simp [PowerSeries.coeff_one]
  | succ d ih => rw [pow_succ, pow_succ]; exact ih.mul fg

private def geometric : PowerSeries ℝ := rescale 4 (invOneSubPow ℝ 1).val

private theorem inverse_power (d : ℕ) : (invOneSubPow ℝ 1).val ^ d = (invOneSubPow ℝ d).val := by
  induction d with
  | zero => simp [invOneSubPow_zero]
  | succ d ih => rw [pow_succ, ih, invOneSubPow_add, Units.val_mul]

private theorem geometric_coeff (d m : ℕ) :
    coeff m (geometric ^ (d+1)) = (4 : ℝ)^m * ((d+m).choose m : ℝ) := by
  rw [geometric, ← map_pow, inverse_power, coeff_rescale,
    invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk, Nat.choose_symm_add]

private theorem product_caps {j : ℕ} (hj : 2 ≤ j) (d m : ℕ) :
    0 ≤ coeff m (V j * H j ^ d) ∧
      coeff m (V j * H j ^ d) ≤ (4 : ℝ)^m * ((d+m).choose m : ℝ) := by
  have term (i : ℕ) : coeff i geometric = (4 : ℝ)^i := by simpa using geometric_coeff 0 i
  have lower : coefficientBound (V j) geometric := fun i ↦ by
    rw [term]
    exact ⟨(V_caps hj i).1, (V_caps hj i).2.trans
      (pow_le_pow_left₀ (by norm_num) (by norm_num) i)⟩
  have upper : coefficientBound (H j) geometric := fun i ↦ by rw [term]; exact H_caps hj i
  have dom := lower.mul (upper.pow d) m
  rw [mul_comm geometric _, ← pow_succ, geometric_coeff] at dom
  exact dom

/-- A single factorial majorant covers every coefficient of every scaled row of positive rank. -/
theorem scaled_coeff_factorial_bound {j d : ℕ} (hj : 2 ≤ j) (hd : 1 ≤ d) (r h : ℕ) :
    0 ≤ scaledReciprocalCoeff j r d h ∧
      scaledReciprocalCoeff j r d h ≤ (4 * ((j+r+1 : ℕ) : ℝ))^(r+j*h) / ((r+j*h).factorial : ℝ) := by
  by_cases hh : h ≤ d
  · rw [scaled_coeff_of_offset hj r hh]
    let m := r+j*h
    let C : ℝ := ((j+r+1 : ℕ) : ℝ)
    have db : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have scale_pos := mul_pos (edgeScale_pos j) db
    have scale_ge : (d : ℝ) ≤ edgeScale j * (d : ℝ) := by
      have slope : 1 ≤ edgeScale j := by
        unfold edgeScale
        linarith only [show 0 ≤ (1 : ℝ) / ((j : ℝ)+1) by positivity]
      simpa using mul_le_mul_of_nonneg_right slope db.le
    have rank_cap : d-h+m ≤ (j+r+1)*d := by
      have size := Nat.mul_le_mul_left j hh
      have offset : r ≤ r*d := by simpa using Nat.mul_le_mul_left r hd
      dsimp [m]
      rw [Nat.add_mul, Nat.add_mul, one_mul]
      omega
    have cap := (product_caps hj (d-h) m).2
    refine ⟨div_nonneg (product_caps hj (d-h) m).1 (by positivity), ?_⟩
    calc
      _ ≤ ((4 : ℝ)^m * ((d-h+m).choose m : ℝ)) / (edgeScale j * (d : ℝ))^m :=
        div_le_div_of_nonneg_right cap (pow_nonneg scale_pos.le _)
      _ ≤ ((4 : ℝ)^m * ((C * (d : ℝ))^m / (m.factorial : ℝ))) / (edgeScale j * (d : ℝ))^m := by
        have choose := Nat.choose_le_pow_div (α := ℝ) m (d-h+m)
        apply div_le_div_of_nonneg_right _ (pow_nonneg scale_pos.le _)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine choose.trans (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ m) (by positivity))
        dsimp [C]
        exact_mod_cast rank_cap
      _ ≤ ((4 : ℝ)^m * ((C * (d : ℝ))^m / (m.factorial : ℝ))) / (d : ℝ)^m :=
        div_le_div_of_nonneg_left (by dsimp [C]; positivity) (pow_pos db _)
          (pow_le_pow_left₀ db.le scale_ge _)
      _ = (4*C)^m / (m.factorial : ℝ) := by
        rw [mul_pow C, mul_pow 4]
        field_simp
  · simp [scaledReciprocalCoeff, hh]; positivity

#print axioms scaled_coeff_factorial_bound

end OrderedPartitions.ReciprocalEdge
