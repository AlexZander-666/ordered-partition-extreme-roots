import OrderedPartitions.ReciprocalEdgeSlopeSigns
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Complex Filter Set OrderedPartitions.ReciprocalEdge
open scoped Topology ComplexConjugate

/-- Actual real restriction of the factorial multisection. -/
def sectionR (j r : ℕ) (x : ℝ) : ℝ := (reciprocalLimit j r x).re

theorem sectionR_cast (j r : ℕ) (x : ℝ) : (sectionR j r x:ℂ) = reciprocalLimit j r x :=
  Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr (section_im_zero j r x))

theorem real_derivative {j : ℕ} (hj : 1≤j) (r : ℕ) (x : ℝ) :
    HasDerivAt (sectionR j r) (deriv (reciprocalLimit j r) (x:ℂ)).re x :=
  (multisection_derivative hj r _).differentiableAt.hasDerivAt.real_of_complex

private theorem upper_ratio {a b : ℂ} (h : 0≤(a*conj b).im) : 0≤(a/b).im := by
  rw [Complex.div_im, ← sub_div]
  apply div_nonneg _ (normSq_nonneg b)
  simpa only [Complex.mul_im, conj_im, conj_re, mul_neg, ← sub_eq_neg_add, mul_comm] using h

theorem ratio_deriv_nonneg {j : ℕ} (hj : 1≤j) (i k : Fin j) (ik : i≤k)
    {x : ℝ} (gx : sectionR j k x≠0) :
    0 ≤ deriv (fun u ↦ sectionR j i u / sectionR j k u) x := by
  let f := reciprocalLimit j i
  let g := reciprocalLimit j k
  let R (z : ℂ) := f z / g z
  have eq (t : ℝ) : R t = ((sectionR j i t / sectionR j k t:ℝ):ℂ) := by
    simp only [R, f, g, ofReal_div, sectionR_cast]
  have gne : g x≠0 := by rw [show g x = (sectionR j k x:ℂ) from (sectionR_cast _ _ _).symm]; exact_mod_cast gx
  have derivR : DifferentiableAt ℂ R (x:ℂ) :=
    (multisection_derivative hj i _).differentiableAt.div (multisection_derivative hj k _).differentiableAt gne
  have sign := boundary_linear_sign (x:=x) (g:=dslope R x) (continuousAt_dslope_same.mpr derivR)
    (Filter.Eventually.of_forall fun w hw ↦ by
      rw [← smul_eq_mul, sub_smul_dslope, sub_im, eq, ofReal_im, sub_zero]
      exact upper_ratio ((actual_chain hj hw.le i k ik).1))
  have re : (fun t : ℝ ↦ (R t).re) = (fun t ↦ sectionR j i t / sectionR j k t) :=
    funext fun t ↦ by rw [eq, ofReal_re]
  rw [← re, derivR.hasDerivAt.real_of_complex.deriv]
  simpa only [dslope_same] using sign

/-- Uniform ordered Wronskians, including points where either section vanishes. -/
theorem wronskian_nonneg {j : ℕ} (hj : 1≤j) (i k : Fin j) (ik : i<k) {x : ℝ} (neg : x<0) :
    0 ≤ deriv (sectionR j i) x * sectionR j k x - sectionR j i x * deriv (sectionR j k) x := by
  by_cases gx : sectionR j k x=0
  · rw [gx, mul_zero, zero_sub, Left.nonneg_neg_iff]
    by_cases fx : sectionR j i x=0
    · rw [fx,zero_mul]
    · have zero : reciprocalLimit j k x=0 := by rw [← sectionR_cast, gx, ofReal_zero]
      have nonzero : reciprocalLimit j i x≠0 := by rw [← sectionR_cast]; exact_mod_cast fx
      have sg := (section_slope_sign hj k i neg zero nonzero).2 ik
      rw [(real_derivative hj k x).deriv, mul_comm]
      exact sg.le
  · have sg := ratio_deriv_nonneg hj i k ik.le gx
    change 0 ≤ deriv (sectionR j i / sectionR j k) x at sg
    rw [((real_derivative hj i x).div (real_derivative hj k x) gx).deriv] at sg
    rw [(real_derivative hj i x).deriv, (real_derivative hj k x).deriv]
    simpa using (le_div_iff₀ (sq_pos_of_ne_zero gx)).mp sg

theorem ratio_monotone {j : ℕ} (hj : 1≤j) (i k : Fin j) (ik : i≤k)
    {s : Set ℝ} (cv : Convex ℝ s) (avoid : ∀ x∈s, sectionR j k x ≠ 0) :
    MonotoneOn (fun x ↦ sectionR j i x / sectionR j k x) s := by
  have dif : ∀ x ∈ s, DifferentiableAt ℝ (fun x ↦ sectionR j i x / sectionR j k x) x :=
    fun x hx ↦ (real_derivative hj i x).differentiableAt.div
      (real_derivative hj k x).differentiableAt (avoid x hx)
  exact monotoneOn_of_deriv_nonneg cv (fun x hx ↦ (dif x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (dif x (interior_subset hx)).differentiableWithinAt)
    (fun x hx ↦ ratio_deriv_nonneg hj i k ik (avoid x (interior_subset hx)))

#print axioms wronskian_nonneg
#print axioms ratio_monotone
end OrderedPartitions.ReciprocalSector
