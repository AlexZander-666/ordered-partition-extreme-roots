import OrderedPartitions.ReciprocalEdgeRealRoots
import Mathlib.Analysis.Calculus.DSlope

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Complex Filter OrderedPartitions.ReciprocalEdge
open scoped Topology ComplexConjugate

theorem section_im_zero (j r : ℕ) (x : ℝ) : (reciprocalLimit j r x).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  simp only [reciprocalLimit, Complex.conj_tsum, map_mul, map_pow, Complex.conj_ofReal]

theorem section_deriv_im_zero {j : ℕ} (hj : 1≤j) (r : ℕ) (x : ℝ) :
    (deriv (reciprocalLimit j r) x).im=0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [(multisection_derivative hj r (x:ℂ)).deriv, Complex.conj_tsum]
  apply tsum_congr
  intro n
  let term : ℂ := (((r+j*(n+1)).factorial:ℂ)⁻¹*((n+1:ℕ):ℂ))*(x:ℂ)^n
  change conj term = term
  unfold term
  simp

private theorem re_ne {z : ℂ} (im : z.im=0) (h : z≠0) : z.re≠0 :=
  fun r ↦ h (Complex.ext (by simpa using r) (by simpa using im))

/-- At a simple zero, the sign of its derivative relative to a nonzero reference
section records on which side in the index chain the reference lies. -/
theorem section_slope_sign {j : ℕ} (hj : 1≤j) (i k : Fin j) {x : ℝ}
    (hx : x<0) (zero : reciprocalLimit j i x=0) (nonzero : reciprocalLimit j k x≠0) :
    (i < k → 0 < (deriv (reciprocalLimit j i) x).re*(reciprocalLimit j k x).re) ∧
    (k < i → (deriv (reciprocalLimit j i) x).re*(reciprocalLimit j k x).re < 0) := by
  let f := reciprocalLimit j i
  let g := reciprocalLimit j k
  let u := dslope f (x:ℂ)
  have cu : ContinuousAt u (x:ℂ) :=
    continuousAt_dslope_same.mpr (multisection_derivative hj i _).differentiableAt
  have cg : ContinuousAt g (x:ℂ) := (multisection_derivative hj k _).continuousAt
  have fac (w : ℂ) : (w-x)*u w=f w := sub_smul_dslope_of_zero zero w
  have allne : (deriv f x).re*(g x).re≠0 :=
    mul_ne_zero (re_ne (section_deriv_im_zero hj i x) (section_simple hj i hx zero))
      (re_ne (section_im_zero j k x) nonzero)
  constructor
  · intro ik
    have h := boundary_linear_sign (x:=x) (g:=fun w ↦ u w*conj (g w)) (cu.mul cg.star)
      (Filter.Eventually.of_forall fun w hw ↦ by
        rw [← mul_assoc, fac]
        exact (actual_chain hj hw.le _ _ ik.le).1)
    have nonneg : 0≤(deriv f x).re*(g x).re := by
      simpa only [u, dslope_same, Complex.mul_re, conj_re, conj_im,
        show (g x).im=0 from section_im_zero j k x, neg_zero, mul_zero, sub_zero] using h
    exact lt_of_le_of_ne nonneg allne.symm
  · intro ki
    have h := boundary_linear_sign (x:=x) (g:=fun w ↦ w*(u w*conj (g w)))
      (continuousAt_id.mul (cu.mul cg.star))
      (Filter.Eventually.of_forall fun w hw ↦ by
        have id : (w-x)*(w*(u w*conj (g w))) = w*f w*conj (g w) := by rw [← fac]; ring
        rw [id]
        exact (actual_chain hj hw.le _ _ ki.le).2)
    have bound : 0≤x*((deriv f x).re*(g x).re) := by
      simpa only [u, dslope_same, Complex.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero,
        conj_re, conj_im, show (g x).im=0 from section_im_zero j k x, neg_zero, mul_zero] using h
    exact lt_of_le_of_ne (nonpos_of_mul_nonneg_right bound hx) allne

#print axioms section_slope_sign
end OrderedPartitions.ReciprocalSector
