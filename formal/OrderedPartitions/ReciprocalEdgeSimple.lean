import OrderedPartitions.ReciprocalEdgeBoundaryOrder
import OrderedPartitions.ReciprocalEdgeSectors
import OrderedPartitions.ReciprocalEdgeMultisections
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Complex Filter OrderedPartitions.ReciprocalEdge
open scoped Topology ComplexConjugate

private theorem upper_div {a b : ℂ} (h : 0≤(a*conj b).im) : 0≤(a/b).im := by
  rw [Complex.div_im, ← sub_div]
  apply div_nonneg _ (normSq_nonneg b)
  simpa only [Complex.mul_im, conj_im, conj_re, mul_neg, ← sub_eq_neg_add,
    mul_comm] using h

private theorem order_unit {f u : ℂ→ℂ} {x : ℝ}
    (af : AnalyticAt ℂ f (x:ℂ)) (au : AnalyticAt ℂ u (x:ℂ)) (nu : u x≠0)
    (nt : ¬∀ᶠ w in 𝓝 (x:ℂ), f w=0)
    (good : ∀ᶠ w in 𝓝 (x:ℂ), 0<w.im → 0≤(f w*u w).im) :
    analyticOrderAt f (x:ℂ) ≤ 1 := by
  have nz := au.continuousAt.eventually_ne nu
  have prod : ¬∀ᶠ w in 𝓝 (x:ℂ), (f*u) w=0 := by
    intro hp
    apply nt
    filter_upwards [hp, nz] with w hw nw
    exact (mul_eq_zero.mp hw).resolve_right nw
  have bound := boundary_order_le_one (f:=f*u) (af.mul au) prod good
  rwa [analyticOrderAt_mul af au, au.analyticOrderAt_eq_zero.mpr nu, add_zero] at bound

private theorem at_origin (j r : ℕ) : reciprocalLimit j r 0 ≠ 0 := by
  have e : reciprocalLimit j r 0 = (r.factorial:ℂ)⁻¹ := by
    unfold reciprocalLimit
    rw [tsum_eq_single 0 (fun i hi ↦ by simp [zero_pow hi])]
    simp
  rw [e]
  exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero r)

/-- Each actual negative zero is simple when the genuine section vector satisfies
the two determinant inequalities on the open upper half-plane. -/
theorem section_simple_of_chain {d : ℕ}
    (chain : ∀ z : ℂ, 0<z.im → AreaChain z (fun r : Fin (d+1) ↦ reciprocalLimit (d+1) r z))
    (i : Fin (d+1)) {x : ℝ} (neg : x<0) (zero : reciprocalLimit (d+1) i x=0) :
    deriv (reciprocalLimit (d+1) i) x ≠ 0 := by
  let F (k : Fin (d+1)) := reciprocalLimit (d+1) k
  have an (k : Fin (d+1)) (z : ℂ) : AnalyticAt ℂ (F k) z := by
    apply Differentiable.analyticAt
    exact fun w ↦ (multisection_derivative (by omega : 1≤d+1) k w).differentiableAt
  obtain ⟨k,hk⟩ := sections_have_no_common_zero (by omega : 1≤d+1) (x:ℂ)
  change F k x ≠ 0 at hk
  have nt : ¬∀ᶠ w in 𝓝 (x:ℂ), F i w=0 := by
    intro h
    have all : F i = fun _ ↦ 0 := AnalyticOnNhd.eq_of_eventuallyEq
      (fun z _ ↦ an i z) (fun _ _ ↦ analyticAt_const) h
    exact at_origin (d+1) i (congrFun all 0)
  have ord : analyticOrderAt (F i) (x:ℂ) ≤ 1 := by
    by_cases order : i≤k
    · apply order_unit (u:=fun z ↦ (F k z)⁻¹) (an i _) ((an k _).inv hk) (inv_ne_zero hk) nt
      exact Filter.Eventually.of_forall fun z hz ↦ by
        simpa only [← div_eq_mul_inv] using upper_div ((chain z hz i k order).1)
    · have nx : (x:ℂ)≠0 := by exact_mod_cast neg.ne
      apply order_unit (u:=fun z ↦ z*(F k z)⁻¹) (an i _)
        (analyticAt_id.mul ((an k _).inv hk)) (mul_ne_zero nx (inv_ne_zero hk)) nt
      exact Filter.Eventually.of_forall fun z hz ↦ by
        have h := upper_div ((chain z hz k i (le_of_not_ge order)).2)
        change 0≤((z*F i z)/F k z).im at h
        simpa only [div_eq_mul_inv, mul_left_comm, mul_assoc, mul_comm] using h
  intro bad
  have lower : (2:ℕ) ≤ analyticOrderAt (F i) (x:ℂ) := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (an i _)).mpr
    intro l hl
    interval_cases l <;> simp [F, zero, bad]
  exact (by decide : ¬(2:ℕ∞)≤1) (lower.trans ord)

#print axioms section_simple_of_chain
end OrderedPartitions.ReciprocalSector
