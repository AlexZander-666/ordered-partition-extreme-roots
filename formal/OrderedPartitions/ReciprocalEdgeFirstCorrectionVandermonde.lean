import OrderedPartitions.ReciprocalEdgeFirstCorrectionSeries
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Bounds

/-! The lower-degree binomial terms admit a first-order factorial majorant. -/

noncomputable section
namespace OrderedPartitions.ReciprocalEdge

open Finset PowerSeries

private def coefficientDominated (f g : PowerSeries ℝ) : Prop :=
  ∀ m, 0 ≤ coeff m f ∧ coeff m f ≤ coeff m g

private theorem coefficientDominated.mul {f g p q : PowerSeries ℝ}
    (fg : coefficientDominated f g) (pq : coefficientDominated p q) :
    coefficientDominated (f*p) (g*q) := by
  intro m
  simp only [coeff_mul]
  exact ⟨sum_nonneg (fun i _ ↦ mul_nonneg (fg i.1).1 (pq i.2).1),
    sum_le_sum (fun i _ ↦ mul_le_mul (fg i.1).2 (pq i.2).2 (pq i.2).1
      ((fg i.1).1.trans (fg i.1).2))⟩

private theorem coefficientDominated.pow {f g : PowerSeries ℝ}
    (fg : coefficientDominated f g) (d : ℕ) : coefficientDominated (f^d) (g^d) := by
  induction d with
  | zero => intro m; cases m <;> simp [PowerSeries.coeff_one]
  | succ d ih => rw [pow_succ, pow_succ]; exact ih.mul fg

private def geometricFour : PowerSeries ℝ := rescale 4 (invOneSubPow ℝ 1).val

private theorem inverse_power (d : ℕ) : (invOneSubPow ℝ 1).val^d = (invOneSubPow ℝ d).val := by
  induction d with
  | zero => simp [invOneSubPow_zero]
  | succ d ih => rw [pow_succ, ih, invOneSubPow_add, Units.val_mul]

private theorem geometricFour_coeff (d m : ℕ) :
    coeff m (geometricFour^(d+1)) = (4:ℝ)^m*((d+m).choose m:ℝ) := by
  rw [geometricFour, ← map_pow, inverse_power, coeff_rescale,
    invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk, Nat.choose_symm_add]

theorem binomial_term_factorial_bound {j : ℕ} (hj : 2 ≤ j) (i k : ℕ) :
    0 ≤ coeff k (V j*L j^i) ∧ coeff k (V j*L j^i) ≤ (4:ℝ)^(i+k)*((i+k).choose k:ℝ) := by
  have geo_coeff (m : ℕ) : coeff m geometricFour = (4:ℝ)^m := by
    simpa using geometricFour_coeff 0 m
  have majorV : coefficientDominated (V j) geometricFour := fun m ↦ by
    rw [geo_coeff]
    have pr := V_first_correction_bounds hj m
    exact ⟨pr.1, pr.2.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) m)⟩
  have majorL : coefficientDominated (L j) (C 4*geometricFour) := fun m ↦ by
    rw [L, coeff_mk, coeff_C_mul, geo_coeff]
    simpa only [pow_succ', mul_comm] using H_first_correction_bounds hj (m+1)
  have together := (majorV.mul (majorL.pow i)) k
  rw [show geometricFour*(C 4*geometricFour)^i =
      C ((4:ℝ)^i)*geometricFour^(i+1) by
      rw [mul_pow, ← map_pow, pow_succ]
      ring, coeff_C_mul, geometricFour_coeff, ← mul_assoc, ← pow_add] at together
  exact together

private theorem choose_difference (D k l : ℕ) :
    (D+l).choose (k+1) ≤ D.choose (k+1) + l*(D+l).choose k := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show D+(l+1)= (D+l)+1 by omega, Nat.choose_succ_succ, Nat.succ_mul]
    have one := Nat.choose_le_choose k (Nat.le_succ (D+l))
    have wider := Nat.mul_le_mul_left l one
    simp only [Nat.succ_eq_add_one] at *
    omega

private theorem vandermonde_lower_sum (D k : ℕ) :
    (∑ i ∈ range (k+1), D.choose i * (k+1).choose (k+1-i)) ≤
      (k+1)*(D+(k+1)).choose k := by
  have exact_sum := Nat.add_choose_eq D (k+1) (k+1)
  rw [Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ] at exact_sum
  simp only [Nat.sub_self, Nat.choose_zero_right, mul_one] at exact_sum
  have increase := choose_difference D k (k+1)
  omega

/-- The lower summands of the binomial formula, before division by the row scale. -/
theorem lower_binomial_tail_bound {j : ℕ} (hj : 2 ≤ j) (D k : ℕ) :
    let m := k+1
    let rest := ∑ i ∈ range m, (D.choose i:ℝ)*coeff (m-i) (V j*L j^i)
    0 ≤ rest ∧ rest ≤ (4:ℝ)^m*(m:ℝ)*((D+m).choose k:ℝ) := by
  dsimp only
  refine ⟨sum_nonneg (fun i _ ↦ mul_nonneg (by positivity)
    (binomial_term_factorial_bound hj i (k+1-i)).1), ?_⟩
  calc
    _ ≤ ∑ i ∈ range (k+1), (D.choose i:ℝ)*
        ((4:ℝ)^(k+1)*((k+1).choose (k+1-i):ℝ)) := by
      apply sum_le_sum
      intro i hi
      have combined := (binomial_term_factorial_bound hj i (k+1-i)).2
      rw [show i+(k+1-i)=k+1 by have := mem_range.mp hi; omega] at combined
      exact mul_le_mul_of_nonneg_left combined (by positivity)
    _ = (4:ℝ)^(k+1)*((∑ i ∈ range (k+1), D.choose i*(k+1).choose (k+1-i):ℕ):ℝ) := by
      push_cast
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have bb := vandermonde_lower_sum D k
      exact_mod_cast bb

#print axioms binomial_term_factorial_bound
#print axioms lower_binomial_tail_bound

end OrderedPartitions.ReciprocalEdge
