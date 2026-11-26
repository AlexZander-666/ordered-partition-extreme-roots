import OrderedPartitions.ReciprocalEdgeFirstCorrectionVandermonde

/-! A rank-independent factorial bound for the first-correction coefficients. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Finset PowerSeries

private theorem edgeScale_ge_one (j : ℕ) : 1 ≤ edgeScale j := by
  unfold edgeScale
  linarith only [show 0 ≤ (1:ℝ)/((j:ℝ)+1) by positivity]

private theorem index_le_two_pow (n : ℕ) : (n:ℝ)+1 ≤ (2:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem square_index_bound (m : ℕ) : (m:ℝ)^2 ≤ (4:ℝ)^m := by
  have cap : (m:ℝ) ≤ (2:ℝ)^m := (le_add_of_nonneg_right zero_le_one).trans (index_le_two_pow m)
  calc
    _ ≤ ((2:ℝ)^m)^2 := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) m) cap 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm m 2, pow_mul]; norm_num

private theorem cost_bound {h m : ℕ} (hm : h ≤ m) : shiftCost h m ≤ 2*(4:ℝ)^m := by
  calc
    shiftCost h m ≤ ∑ _i ∈ range m, 2*(m:ℝ) := by
      apply sum_le_sum
      intro i hi
      have hk : h+i ≤ 2*m := by have := mem_range.mp hi; omega
      exact_mod_cast hk
    _ = 2*(m:ℝ)^2 := by simp [nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (square_index_bound m) (by norm_num)

private theorem normalized_tail {j d h C : ℕ} (hj : 2 ≤ j) (hd : 0 < d) (hC : 1 ≤ C)
    (k : ℕ) (rank_cap : d-h+(k+1) ≤ C*d) :
    let m := k+1
    let rest := ∑ i ∈ range m, ((d-h).choose i:ℝ)*coeff (m-i) (V j*L j^i)
    (d:ℝ)*(rest/(edgeScale j*(d:ℝ))^m) ≤
      (4*(C:ℝ))^m*(m:ℝ)^2/(m.factorial:ℝ) := by
  dsimp only
  let rest := ∑ i ∈ range (k+1), ((d-h).choose i:ℝ)*coeff (k+1-i) (V j*L j^i)
  let c : ℝ := C
  change (d:ℝ)*(rest/(edgeScale j*(d:ℝ))^(k+1)) ≤
    (4*c)^(k+1)*((k+1:ℕ):ℝ)^2/((k+1:ℕ).factorial:ℝ)
  have cp : 1 ≤ c := by dsimp [c]; exact_mod_cast hC
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  have scaled : (d:ℝ) ≤ edgeScale j*(d:ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (edgeScale_ge_one j) dp.le
  obtain ⟨rp, tail⟩ := lower_binomial_tail_bound hj (d-h) k
  have chooseCap : ((d-h+(k+1)).choose k:ℝ) ≤ (c*(d:ℝ))^k/(k.factorial:ℝ) := by
    refine (Nat.choose_le_pow_div (α := ℝ) k (d-h+(k+1))).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by positivity) _ k
    have bound : ((d-h+(k+1):ℕ):ℝ) ≤ ((C*d:ℕ):ℝ) := by exact_mod_cast rank_cap
    simpa only [Nat.cast_mul, c] using bound
  have rest_cap : rest ≤ (4:ℝ)^(k+1)*((k+1:ℕ):ℝ)*((c*(d:ℝ))^k/(k.factorial:ℝ)) :=
    tail.trans (mul_le_mul_of_nonneg_left chooseCap (by positivity))
  calc
    _ ≤ (d:ℝ)*(rest/(d:ℝ)^(k+1)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left rp (pow_pos dp _) (pow_le_pow_left₀ dp.le scaled _)) dp.le
    _ ≤ (d:ℝ)*(((4:ℝ)^(k+1)*((k+1:ℕ):ℝ)*((c*(d:ℝ))^k/(k.factorial:ℝ)))/
        (d:ℝ)^(k+1)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right rest_cap (by positivity)) dp.le
    _ = (4:ℝ)^(k+1)*c^k*((k+1:ℕ):ℝ)/(k.factorial:ℝ) := by
      rw [mul_pow, pow_succ (d:ℝ) k]
      field_simp [dp.ne']
    _ ≤ (4*c)^(k+1)*((k+1:ℕ):ℝ)/(k.factorial:ℝ) := by
      rw [mul_pow]
      gcongr
      omega
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp

private theorem normalized_error {j d h C : ℕ} (hj : 2 ≤ j) (hd : 0 < d) (hC : 1 ≤ C)
    (m : ℕ) (rank_cap : d-h+m ≤ C*d) :
    (d:ℝ)*|coeff m (V j*H j^(d-h))/(edgeScale j*(d:ℝ))^m-1/(m.factorial:ℝ)| ≤
      shiftCost h m/(m.factorial:ℝ)+(4*(C:ℝ))^m*(m:ℝ)^2/(m.factorial:ℝ) := by
  let b := edgeScale j
  have bp : 0 < b := edgeScale_pos j
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  cases m with
  | zero =>
    simp [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply (V j),
      ← coeff_zero_eq_constantCoeff_apply (H j), V_zero hj, H_zero hj, shiftCost]
  | succ k =>
    let m := k+1
    let rest := ∑ i ∈ range m, ((d-h).choose i:ℝ)*coeff (m-i) (V j*L j^i)
    let y := rest/(b*(d:ℝ))^m
    let F := shiftedFalling h m d
    have norm_tail : (d:ℝ)*y ≤ (4*(C:ℝ))^m*(m:ℝ)^2/(m.factorial:ℝ) :=
      normalized_tail hj hd hC k rank_cap
    have yp : 0 ≤ y :=
      div_nonneg (lower_binomial_tail_bound hj (d-h) k).1 (by positivity)
    have extract : coeff m (V j*H j^(d-h))/(b*(d:ℝ))^m =
        F/(m.factorial:ℝ)+y := by
      rw [H_eq_one_add_X_mul hj, fixed_coeff, sum_range_succ]
      simp only [Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
        ← coeff_zero_eq_constantCoeff_apply (V j), ← coeff_zero_eq_constantCoeff_apply (L j),
        V_zero hj, L_zero hj, one_mul]
      change (rest+((d-h).choose m:ℝ)*b^m)/(b*(d:ℝ))^m = _
      rw [add_div, add_comm, mul_pow, mul_comm (((d-h).choose m:ℕ):ℝ), mul_div_mul_left _ _ (pow_ne_zero _ bp.ne')]
      simp only [shifted_choose_ratio, F, y, mul_pow]
    obtain ⟨_, F1, Fcost⟩ := shiftedFalling_bounds h m hd
    change (d:ℝ)*|coeff m (V j*H j^(d-h))/(b*(d:ℝ))^m-1/(m.factorial:ℝ)| ≤ _
    rw [extract, add_sub_right_comm]
    have neg : F/(m.factorial:ℝ)-1/(m.factorial:ℝ) ≤ 0 :=
      sub_nonpos.mpr (div_le_div_of_nonneg_right F1 (by positivity))
    calc
      _ ≤ (d:ℝ)*(|F/(m.factorial:ℝ)-1/(m.factorial:ℝ)|+|y|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) dp.le
      _ = ((d:ℝ)*(1-F))/(m.factorial:ℝ)+(d:ℝ)*y := by
        rw [abs_of_nonpos neg, abs_of_nonneg yp]
        ring
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right Fcost (by positivity)) norm_tail

/-- Uniform control of the first corrections, including reversed indices
beyond the finite degree of the reciprocal polynomial. -/
theorem first_correction_factorial_bound {j d : ℕ} (hj : 2 ≤ j) (hd : 1 ≤ d) (r h : ℕ) :
    let m := r+j*h
    let C := ((j+r+1:ℕ):ℝ)
    (d:ℝ)*|scaledReciprocalCoeff j r d h-1/(m.factorial:ℝ)| ≤
      3*(16*C)^m/(m.factorial:ℝ) := by
  let m := r+j*h
  let C : ℕ := j+r+1
  change (d:ℝ)*|scaledReciprocalCoeff j r d h-1/(m.factorial:ℝ)| ≤
    3*(16*(C:ℝ))^m/(m.factorial:ℝ)
  have C1 : 1 ≤ (C:ℝ) := by exact_mod_cast (by dsimp [C]; omega : 1≤C)
  have cm : h ≤ m := by
    have t := Nat.mul_le_mul_right h (by omega : 1≤j)
    simpa [m] using t.trans (Nat.le_add_left (j*h) r)
  have base : (4:ℝ) ≤ 16*(C:ℝ) := by linarith
  have powers := pow_le_pow_left₀ (by norm_num) base m
  by_cases hh : h ≤ d
  · have rank_cap : d-h+m ≤ C*d := by
      have size := Nat.mul_le_mul_left j hh
      have offset : r ≤ r*d := by simpa using Nat.mul_le_mul_left r hd
      dsimp [m, C]
      rw [Nat.add_mul, Nat.add_mul, one_mul]
      omega
    rw [scaled_coeff_of_offset hj r hh]
    refine (normalized_error hj (by omega) (by dsimp [C]; omega) m rank_cap).trans ?_
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      _ ≤ 2*(4:ℝ)^m+(4*(C:ℝ))^m*(4:ℝ)^m :=
        add_le_add (cost_bound cm) (mul_le_mul_of_nonneg_left (square_index_bound m) (by positivity))
      _ = 2*(4:ℝ)^m+(16*(C:ℝ))^m := by
        rw [← mul_pow, show 4*(C:ℝ)*4 = 16*(C:ℝ) by ring]
      _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left powers (show (0:ℝ)≤2 by norm_num)]
  · rw [scaledReciprocalCoeff, if_neg hh, zero_sub, abs_neg, abs_of_nonneg (by positivity : 0≤1/(m.factorial:ℝ))]
    simp only [← mul_div_assoc, mul_one]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have bound : (d:ℝ) ≤ m := by exact_mod_cast (by omega : d≤m)
    have index : (m:ℝ) ≤ (2:ℝ)^m := (le_add_of_nonneg_right zero_le_one).trans (index_le_two_pow m)
    have grows : (2:ℝ)^m ≤ (16*(C:ℝ))^m := pow_le_pow_left₀ (by norm_num) (by linarith) m
    exact (bound.trans (index.trans grows)).trans (by linarith [show (0:ℝ)≤(16*(C:ℝ))^m by positivity])

#print axioms first_correction_factorial_bound

end OrderedPartitions.ReciprocalEdge
