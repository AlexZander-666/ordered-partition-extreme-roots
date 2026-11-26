import OrderedPartitions.ReciprocalEdgeWronskian

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Complex Filter Set OrderedPartitions.ReciprocalEdge
open scoped Topology

theorem zero_cast {j r : ℕ} {x : ℝ} :
    sectionR j r x=0 ↔ reciprocalLimit j r x=0 := by rw [←sectionR_cast]; simp

theorem real_simple {j : ℕ} (hj : 1≤j) (r : Fin j) {x : ℝ} (hx : x<0)
    (zero : sectionR j r x=0) : deriv (sectionR j r) x≠0 := by
  rw [(real_derivative hj r x).deriv]
  intro eq
  apply section_simple hj r hx (zero_cast.mp zero)
  exact Complex.ext (by simpa using eq) (by simpa using section_deriv_im_zero hj r x)

theorem sectionR_zero_pos (j r : ℕ) : 0<sectionR j r 0 := by
  have e : reciprocalLimit j r 0 = (r.factorial:ℂ)⁻¹ := by
    unfold reciprocalLimit
    rw [tsum_eq_single 0 (fun h non ↦ by simp [zero_pow non])]
    simp
  have invpos : 0<(r.factorial:ℝ)⁻¹ := by positivity
  change 0<(reciprocalLimit j r ((0:ℝ):ℂ)).re
  rw [ofReal_zero,e, ← ofReal_natCast, ← ofReal_inv, ofReal_re]
  exact invpos

private theorem around_pole {f g : ℝ→ℝ} {x : ℝ} (cf : ContinuousAt f x)
    (dg : DifferentiableAt ℝ g x) (zero : g x=0) (residue : f x*deriv g x<0) :
    ∀ᶠ y in 𝓝 x, y≠x → (f y/g y)*(y-x)<0 := by
  have ds : ContinuousAt (dslope g x) x := continuousAt_dslope_same.mpr dg
  have neg : (fun y ↦ f y/dslope g x y) x<0 := by
    change f x/dslope g x x<0
    rw [dslope_same]; exact (div_neg_iff.mpr (mul_neg_iff.mp residue))
  have continuous := cf.div ds (by rw [dslope_same]; exact right_ne_zero_of_mul (ne_of_lt residue))
  filter_upwards [continuous.eventually_lt continuousAt_const neg] with y hy ne
  change f y/dslope g x y<0 at hy
  have dy : dslope g x y≠0 := by rintro h; rw [h,div_zero] at hy; linarith
  have factor : (y-x)*dslope g x y=g y := sub_smul_dslope_of_zero zero y
  rw [← factor]
  have z : y-x≠0 := sub_ne_zero.mpr ne
  convert hy using 1
  field_simp

/-- On an interval free of poles, the numerator has at most one negative zero. -/
theorem unique_on_gap {j : ℕ} (hj : 1≤j) (i k : Fin j) (ik : i≤k)
    {a b : ℝ} (bn : b≤0) (clear : ∀ x∈Ioo a b, sectionR j k x ≠ 0)
    {u v : ℝ} (hu : u∈Ioo a b) (hv : v∈Ioo a b) (fu : sectionR j i u=0)
    (fv : sectionR j i v=0) : u=v := by
  have rule {u v : ℝ} (hu : u∈Ioo a b) (hv : v∈Ioo a b) (huv : u<v)
      (fu : sectionR j i u=0) (fv : sectionR j i v=0) : False := by
    let m := (u+v)/2
    have um : u<m := by dsimp [m]; linarith
    have mv : m<v := by dsimp [m]; linarith
    have mono := ratio_monotone hj i k ik (convex_Ioo a b) clear
    have flat (y : ℝ) (hy : y∈Ioo u v) : sectionR j i y=0 := by
      have loc : y∈Ioo a b := ⟨hu.1.trans hy.1,hy.2.trans hv.2⟩
      have low := mono hu loc hy.1.le
      have high := mono loc hv hy.2.le
      simp only [fu,fv,zero_div] at low high
      exact (div_eq_zero_iff.mp (le_antisymm high low)).resolve_right (clear y loc)
    have eq : sectionR j i =ᶠ[𝓝 m] fun _ ↦ 0 := by
      filter_upwards [isOpen_Ioo.mem_nhds (show m∈Ioo u v from ⟨um,mv⟩)] with y hy
      exact flat y hy
    have der : deriv (sectionR j i) m=0 := by simpa using eq.deriv_eq
    exact real_simple hj i ((mv.trans hv.2).trans_le bn) (flat m ⟨um,mv⟩) der
  exact le_antisymm (le_of_not_gt fun h ↦ rule hv hu h fv fu)
    (le_of_not_gt fun h ↦ rule hu hv h fu fv)

private theorem residue_sign {j : ℕ} (hj : 1≤j) (i k : Fin j) (ik : i<k)
    {a : ℝ} (neg : a<0) (pole : sectionR j k a=0) (nz : sectionR j i a≠0) :
    ∀ᶠ y in 𝓝 a, y≠a → (sectionR j i y/sectionR j k y)*(y-a)<0 := by
  apply around_pole (real_derivative hj i _).continuousAt (real_derivative hj k _).differentiableAt pole
  rw [(real_derivative hj k _).deriv, mul_comm]
  exact (section_slope_sign hj k i neg (zero_cast.mp pole) (mt zero_cast.mpr nz)).2 ik

private theorem one_between {j : ℕ} (hj : 1≤j) (i k : Fin j) {a b : ℝ}
    (ab : a<b) (avoid : ∀ x∈Icc a b, sectionR j k x≠0)
    (low : sectionR j i a/sectionR j k a < 0) (high : 0<sectionR j i b/sectionR j k b) :
    ∃ x∈Ioo a b, sectionR j i x=0 := by
  have cont : ContinuousOn (fun x ↦ sectionR j i x / sectionR j k x) (Icc a b) :=
    fun x hx ↦ ((real_derivative hj i x).continuousAt.div (real_derivative hj k x).continuousAt
      (avoid x hx)).continuousWithinAt
  obtain ⟨p,hp,zero⟩ := intermediate_value_Ioo ab.le cont ⟨low,high⟩
  exact ⟨p,hp,(div_eq_zero_iff.mp zero).resolve_right (avoid p ⟨hp.1.le,hp.2.le⟩)⟩

theorem zero_between_poles {j : ℕ} (hj : 1≤j) (i k : Fin j) (ik : i<k)
    {a b : ℝ} (ab : a<b) (bn : b<0)
    (pa : sectionR j k a=0) (pb : sectionR j k b=0)
    (na : sectionR j i a≠0) (nb : sectionR j i b≠0)
    (clear : ∀ x∈Ioo a b, sectionR j k x≠0) :
    ∃! x, x∈Ioo a b ∧ sectionR j i x=0 := by
  obtain ⟨m,am,mb⟩ := exists_between ab
  have leftE : ∀ᶠ y in 𝓝[>] a, a<y ∧ y<m ∧ (sectionR j i y/sectionR j k y)*(y-a)<0 := by
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds am).filter_mono nhdsWithin_le_nhds,
      (residue_sign hj i k ik (ab.trans bn) pa na).filter_mono nhdsWithin_le_nhds] with y ha hm hy
    exact ⟨ha,hm,hy (ne_of_gt ha)⟩
  have rightE : ∀ᶠ y in 𝓝[<] b, y<b ∧ m<y ∧ (sectionR j i y/sectionR j k y)*(y-b)<0 := by
    filter_upwards [self_mem_nhdsWithin, (lt_mem_nhds mb).filter_mono nhdsWithin_le_nhds,
      (residue_sign hj i k ik bn pb nb).filter_mono nhdsWithin_le_nhds] with y hb hm hy
    exact ⟨hb,hm,hy (ne_of_lt hb)⟩
  obtain ⟨l,al,lm,hl⟩ := leftE.exists
  obtain ⟨r,rb,mr,hr⟩ := rightE.exists
  have low := neg_of_mul_neg_left hl (sub_pos.mpr al).le
  have high := pos_of_mul_neg_left hr (sub_neg.mpr rb).le
  obtain ⟨x,⟨lx,xr⟩,fx⟩ := one_between hj i k (lm.trans mr)
    (fun y hy ↦ clear y ⟨al.trans_le hy.1,hy.2.trans_lt rb⟩) low high
  have loc : x∈Ioo a b := ⟨al.trans lx,xr.trans rb⟩
  exact ⟨x,⟨loc,fx⟩, fun _ h ↦ unique_on_gap hj i k ik.le bn.le clear h.1 loc h.2 fx⟩

/-- Exactly one numerator root lies between the rightmost denominator root and zero. -/
theorem zero_after_last_pole {j : ℕ} (hj : 1≤j) (i k : Fin j) (ik : i<k)
    {a : ℝ} (an : a<0) (pole : sectionR j k a=0) (nz : sectionR j i a≠0)
    (clear : ∀ x∈Ioo a 0, sectionR j k x≠0) :
    ∃! x, x∈Ioo a 0 ∧ sectionR j i x=0 := by
  have leftE : ∀ᶠ y in 𝓝[>] a, a<y ∧ y<0 ∧ (sectionR j i y/sectionR j k y)*(y-a)<0 := by
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds an).filter_mono nhdsWithin_le_nhds,
      (residue_sign hj i k ik an pole nz).filter_mono nhdsWithin_le_nhds] with y ha hn hy
    exact ⟨ha,hn,hy (ne_of_gt ha)⟩
  obtain ⟨l,al,ln,hl⟩ := leftE.exists
  have avoid (y : ℝ) (hy : y∈Icc l 0) : sectionR j k y ≠ 0 := by
    rcases hy.2.eq_or_lt with e|lt
    · subst y; exact (sectionR_zero_pos _ _).ne'
    · exact clear y ⟨al.trans_le hy.1,lt⟩
  obtain ⟨x,⟨lx,xn⟩,fx⟩ := one_between hj i k ln avoid
    (neg_of_mul_neg_left hl (sub_pos.mpr al).le)
    (div_pos (sectionR_zero_pos _ _) (sectionR_zero_pos _ _))
  have loc : x∈Ioo a 0 := ⟨al.trans lx,xn⟩
  exact ⟨x,⟨loc,fx⟩,fun _ h ↦ unique_on_gap hj i k ik.le le_rfl clear h.1 loc h.2 fx⟩

#print axioms zero_after_last_pole
#print axioms unique_on_gap
#print axioms zero_between_poles
end OrderedPartitions.ReciprocalSector
