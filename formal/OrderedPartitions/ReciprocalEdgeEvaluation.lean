import OrderedPartitions.ReciprocalEdgeRowLimit
import Mathlib.Algebra.Polynomial.Reverse

/-! The scaled polynomial and the reciprocal substitution in the original row. -/

noncomputable section
open Finset

namespace OrderedPartitions.ReciprocalEdge

def reciprocalArgumentScale (j d : ℕ) : ℝ :=
  (j.factorial : ℝ) * (edgeScale j * (d : ℝ))^j

def reciprocalPrefactor (j r d : ℕ) : ℝ :=
  (j.factorial : ℝ)^d / (((j*d+r).factorial : ℝ) * (edgeScale j * (d : ℝ))^r)

theorem reciprocalArgumentScale_pos (j : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    0 < reciprocalArgumentScale j d := by
  have positive : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have slope := edgeScale_pos j
  unfold reciprocalArgumentScale
  positivity

private theorem degree_bound {j r d : ℕ} (hj : 1 ≤ j) (hr : r < j) :
    (row (j*d+r) j).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k high
  have first : j*d+r < (d+1)*j := by
    rw [Nat.add_mul, Nat.mul_comm d j, one_mul]
    exact Nat.add_lt_add_left hr _
  rw [coeff_row hj, count_above_degree hj (first.trans_le (Nat.mul_le_mul_right j high))]
  norm_num

private theorem scaled_coeff_paper (j r : ℕ) {d h : ℕ} (hd : 1 ≤ d) (hh : h ≤ d) :
    scaledReciprocalCoeff j r d h = reciprocalPrefactor j r d *
      (row (j*d+r) j).coeff (d-h) / (reciprocalArgumentScale j d)^h := by
  have positive : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have slope := edgeScale_pos j
  have fact : (j.factorial : ℝ)^d = (j.factorial : ℝ)^(d-h) * (j.factorial : ℝ)^h := by
    rw [← pow_add, Nat.sub_add_cancel hh]
  rw [scaledReciprocalCoeff, if_pos hh, reciprocalPrefactor, reciprocalArgumentScale,
    fact, pow_add (edgeScale j * (d : ℝ)) r (j*h), pow_mul (edgeScale j * (d : ℝ)) j h,
    mul_pow (j.factorial : ℝ) ((edgeScale j * (d : ℝ))^j) h]
  field_simp

/-- At a nonzero argument, the polynomial extension equals the rescaled true row
at the reciprocal argument. The formula also applies over the complex numbers. -/
theorem eval₂_reciprocalRow {S : Type*} [Field S] [Algebra ℝ S] {j r d : ℕ}
    (hj : 2 ≤ j) (hr : r < j) (hd : 1 ≤ d) (w : S) (hw : w ≠ 0) :
    (reciprocalRow j r d).eval₂ (algebraMap ℝ S) w =
      algebraMap ℝ S (reciprocalPrefactor j r d) *
      (w / algebraMap ℝ S (reciprocalArgumentScale j d))^d *
      (row (j*d+r) j).eval₂ (algebraMap ℝ S) (algebraMap ℝ S (reciprocalArgumentScale j d) / w) := by
  let f := algebraMap ℝ S
  let p := row (j*d+r) j
  let a := reciprocalArgumentScale j d
  let s := f a
  let v := f (reciprocalPrefactor j r d)
  have deg : p.natDegree ≤ d := degree_bound (by omega) hr
  have sn : s ≠ 0 := (map_ne_zero f).2 (reciprocalArgumentScale_pos j hd).ne'
  have reflected_range : (Polynomial.map f (p.reflect d)).natDegree < d+1 := by
    have lab : (Polynomial.map f (p.reflect d)).natDegree ≤ (p.reflect d).natDegree :=
      Polynomial.natDegree_map_le
    exact Nat.lt_succ_of_le (lab.trans (Polynomial.natDegree_reflect_le.trans (max_le le_rfl deg)))
  have scaled : (reciprocalRow j r d).eval₂ f w = v * (p.reflect d).eval₂ f (w/s) := by
    conv_rhs => rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval_eq_sum_range' reflected_range]
    rw [reciprocalRow, Polynomial.eval₂_finsetSum, mul_sum]
    apply sum_congr rfl
    intro h hh
    have le := Nat.le_of_lt_succ (mem_range.mp hh)
    rw [Polynomial.eval₂_monomial, Polynomial.coeff_map, Polynomial.coeff_reflect,
      Polynomial.revAt_le le, scaled_coeff_paper j r hd le]
    rw [map_div₀ f, map_mul f, map_pow f, div_pow]
    dsimp only [p, s, a, v]
    ring
  have probe := div_ne_zero sn hw
  let _ : Invertible (s/w) := invertibleOfNonzero probe
  have reflect := Polynomial.eval₂_reflect_mul_pow f (s/w) d p deg
  rw [invOf_eq_inv, inv_div] at reflect
  have reversed : (p.reflect d).eval₂ f (w/s) = (w/s)^d * p.eval₂ f (s/w) := by
    calc
      _ = p.eval₂ f (s/w) / (s/w)^d := (eq_div_iff (pow_ne_zero d probe)).mpr reflect
      _ = p.eval₂ f (s/w) * ((s/w)^d)⁻¹ := div_eq_mul_inv _ _
      _ = _ := by rw [← inv_pow, inv_div, mul_comm]
  rw [scaled, reversed, ← mul_assoc]

#print axioms reciprocalArgumentScale_pos
#print axioms eval₂_reciprocalRow

end OrderedPartitions.ReciprocalEdge
