import OrderedPartitions.ReciprocalEdgeCyclicPrimitives
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! Infinitely many zeros from the cyclic real derivative system. -/
noncomputable section
namespace OrderedPartitions.ReciprocalEdge
open Set Filter
open scoped Topology

private def FarZeros (f : ℝ → ℝ) : Prop := ∀ b, ∃ x, b < x ∧ f x = 0

private theorem rolle_far {f g : ℝ → ℝ} (d : ∀ t, HasDerivAt g (f t) t)
    (many : FarZeros g) : FarZeros f := by
  intro b
  obtain ⟨x,bx,hx⟩ := many b
  obtain ⟨y,xy,hy⟩ := many x
  obtain ⟨z,hz,zero⟩ := exists_hasDerivAt_eq_zero xy
    (fun t _ ↦ (d t).continuousAt.continuousWithinAt) (hx.trans hy.symm) (fun t _ ↦ d t)
  exact ⟨z,bx.trans hz.1,zero⟩

private theorem tail_sign {f : ℝ → ℝ} (hf : Continuous f) (few : ¬ FarZeros f) :
    (∀ᶠ x in atTop, 0 < f x) ∨ (∀ᶠ x in atTop, f x < 0) := by
  unfold FarZeros at few
  push Not at few
  obtain ⟨b,hb⟩ := few
  let T := b+1
  have bt : b<T := by dsimp [T]; linarith
  rcases lt_or_gt_of_ne (hb T bt) with neg | pos
  · right
    filter_upwards [eventually_ge_atTop T] with t ht
    by_contra! h
    obtain ⟨z,hz,ze⟩ := intermediate_value_Icc ht hf.continuousOn (show 0∈Icc (f T) (f t) from ⟨neg.le,h⟩)
    exact hb z (bt.trans_le hz.1) ze
  · left
    filter_upwards [eventually_ge_atTop T] with t ht
    by_contra! h
    obtain ⟨z,hz,ze⟩ := intermediate_value_Icc' ht hf.continuousOn (show 0∈Icc (f t) (f T) from ⟨h,pos.le⟩)
    exact hb z (bt.trans_le hz.1) ze

private theorem upper_tail {f : ℝ → ℝ} {v T : ℝ}
    (mono : MonotoneOn f (Ici T) ∨ AntitoneOn f (Ici T))
    (small : ¬ ∀ᶠ t in atTop, v ≤ f t) : ∀ᶠ t in atTop, f t < v := by
  rcases mono with up | down
  · filter_upwards [eventually_ge_atTop T] with t ht
    by_contra! hv
    apply small
    filter_upwards [eventually_ge_atTop t] with s hs
    exact hv.trans (up ht (ht.trans hs) hs)
  · have ex : ∃ t, T ≤ t ∧ f t < v := by
      by_contra! h
      exact small (eventually_atTop.mpr ⟨T,h⟩)
    obtain ⟨t,ht,hv⟩ := ex
    filter_upwards [eventually_ge_atTop t] with s hs
    exact (down ht (ht.trans hs) hs).trans_lt hv

private theorem mono_primitive {f g : ℝ → ℝ} (d : ∀ t, HasDerivAt g (f t) t)
    (sgn : (∀ᶠ t in atTop, 0<f t) ∨ (∀ᶠ t in atTop, f t<0)) :
    ∃ T, MonotoneOn g (Ici T) ∨ AntitoneOn g (Ici T) := by
  rcases sgn with pos | neg
  · obtain ⟨T,h⟩ := eventually_atTop.mp pos
    exact ⟨T,Or.inl (monotoneOn_of_deriv_nonneg (convex_Ici _) (fun x _ ↦ (d x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (d x).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (d x).deriv ▸ (h x (interior_subset hx)).le))⟩
  · obtain ⟨T,h⟩ := eventually_atTop.mp neg
    exact ⟨T,Or.inr (antitoneOn_of_deriv_nonpos (convex_Ici _) (fun x _ ↦ (d x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (d x).differentiableAt.differentiableWithinAt)
      (fun x hx ↦ (d x).deriv ▸ (h x (interior_subset hx)).le))⟩

private theorem cyclic_far {j : ℕ} (jp : 0<j) (F : ℕ→ℝ→ℝ)
    (der : ∀ n t,HasDerivAt (F (n+1)) (F n t) t)
    (flip : ∀ n t, F (n+j) t = -F n t)
    (nondecay : ¬ ∀ n, Tendsto (F n) atTop (𝓝 0)) (m : ℕ) : FarZeros (F m) := by
  by_contra few
  have later (k : ℕ) : ¬ FarZeros (F (m+k)) := by
    induction k with
    | zero => simpa using few
    | succ k ih => exact fun many ↦ ih (rolle_far (der (m+k)) many)
  have liftZeros (n k : ℕ) (h : FarZeros (F n)) : FarZeros (F (n+j*k)) := by
    induction k with
    | zero => simpa using h
    | succ k ih =>
      rw [Nat.mul_succ, ←Nat.add_assoc]
      intro b
      obtain ⟨x,hx,z⟩ := ih b
      exact ⟨x,hx,by rw [flip,z,neg_zero]⟩
  have none (n : ℕ) : ¬ FarZeros (F n) := by
    intro h
    have ge : m≤n+j*m := by nlinarith [Nat.one_le_iff_ne_zero.mpr jp.ne']
    have bad := later (n+j*m-m)
    rw [Nat.add_sub_of_le ge] at bad
    exact bad (liftZeros n m h)
  have cont (n : ℕ) : Continuous (F n) := by
    have c : Continuous (F (n+j-1+1)) := continuous_iff_continuousAt.mpr (fun x ↦ (der (n+j-1) x).continuousAt)
    rw [show n+j-1+1=n+j by omega] at c
    simpa only [show F (n+j) = -F n from funext (flip n),neg_neg] using c.neg
  have negDer (n : ℕ) (t : ℝ) : HasDerivAt (fun s ↦ -F (n+1) s) (-F n t) t := (der n t).neg
  have negFlip (n : ℕ) (t : ℝ) : -F (n+j) t = - -F n t := by rw [flip]
  have lim (n : ℕ) : Tendsto (F (n+1)) atTop (𝓝 0) := by
    obtain ⟨T,mono⟩ := mono_primitive (der n) (tail_sign (cont n) (none n))
    apply tendsto_order.mpr
    constructor
    · intro a ha
      have nm : MonotoneOn (-F (n+1)) (Ici T) ∨ AntitoneOn (-F (n+1)) (Ici T) := by
        rcases mono with up|down
        · exact Or.inr fun _ hx _ hy h ↦ neg_le_neg (up hx hy h)
        · exact Or.inl fun _ hx _ hy h ↦ neg_le_neg (down hx hy h)
      have small := upper_tail nm (no_positive_tail jp (fun n t ↦ -F n t) negDer negFlip (n+1) (neg_pos.mpr ha))
      simpa using small
    · intro b hb
      exact upper_tail mono (no_positive_tail jp F der flip (n+1) hb)
  apply nondecay
  intro n
  have l := (lim (n+j-1)).neg
  rw [show n+j-1+1=n+j by omega,show F (n+j) = -F n from funext (flip n)] at l
  simpa using l


/-- Each limiting residue class has real zeros arbitrarily far down the negative axis. -/
theorem unbounded_section_zeros {j : ℕ} (hj : 2≤j) (r : Fin j) (b : ℝ) :
    ∃ a : ℝ, a < b ∧ reciprocalLimit j r a=0 := by
  have eq (s : Fin j) : signedSection j s = oscillatingSection j s := by
    funext t
    simp [signedSection,Nat.div_eq_of_lt s.isLt,Nat.mod_eq_of_lt s.isLt]
  have many := cyclic_far (by omega : 0<j) (signedSection j) (signed_deriv hj) (signed_shift hj)
    (fun h ↦ oscillator_not_all_decay hj (fun s ↦ eq s ▸ h s)) r
  obtain ⟨t,ht,hz⟩ := many (max 1 (-b))
  have gt : 1<t := (le_max_left _ _).trans_lt ht
  have away : -b<t := (le_max_right _ _).trans_lt ht
  have power : t≤t^j := le_self_pow₀ gt.le (by omega)
  refine ⟨-(t^j),by linarith,?_⟩
  rw [eq] at hz
  have hre : (reciprocalLimit j r ((-(t^j):ℝ):ℂ)).re=0 :=
    (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (by linarith : t≠0))
  have hconj := section_conj j r ((-(t^j):ℝ):ℂ)
  have heq : star (reciprocalLimit j r ((-(t^j):ℝ):ℂ)) = reciprocalLimit j r ((-(t^j):ℝ):ℂ) := by
    simpa using hconj.symm
  obtain ⟨y,ey⟩ := Complex.conj_eq_iff_real.mp heq
  rw [ey] at hre ⊢
  exact_mod_cast hre

#print axioms unbounded_section_zeros
end OrderedPartitions.ReciprocalEdge
