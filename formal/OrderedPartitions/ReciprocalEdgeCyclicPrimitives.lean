import OrderedPartitions.ReciprocalEdgeOscillator

/-! Cyclic primitives for the real restrictions of the limiting multisections. -/
noncomputable section
namespace OrderedPartitions.ReciprocalEdge
open Filter Set
open scoped Topology

/-- Extending the index by one period negates the oscillating section. Its derivative lowers
the index by one without a sign, including at a wraparound. -/
def signedSection (j n : ℕ) (t : ℝ) : ℝ := (-1:ℝ)^(n/j)*oscillatingSection j (n%j) t

theorem signed_shift {j : ℕ} (hj : 2≤j) (n : ℕ) (t : ℝ) :
    signedSection j (n+j) t= -signedSection j n t := by
  simp [signedSection,Nat.add_div_right _ (by omega : 0<j),Nat.add_mod_right,pow_succ]

theorem signed_deriv {j : ℕ} (hj : 2≤j) (n : ℕ) (t : ℝ) :
    HasDerivAt (signedSection j (n+1)) (signedSection j n t) t := by
  change HasDerivAt (fun s ↦ (-1:ℝ)^((n+1)/j)*oscillatingSection j ((n+1)%j) s) _ t
  have jp : 0<j := by omega
  have ml := Nat.mod_lt n jp
  have one : 1%j=1 := Nat.mod_eq_of_lt (by omega)
  have div1 : 1/j=0 := Nat.div_eq_of_lt (by omega)
  have dv := Nat.add_div (a:=n) (b:=1) jp
  rw [div1,one,Nat.add_zero] at dv
  by_cases lt : n%j+1<j
  · rw [if_neg (not_le.mpr lt),Nat.add_zero] at dv
    have rem : (n+1)%j=n%j+1 := by rw [Nat.add_mod,one,Nat.mod_eq_of_lt lt]
    simpa only [signedSection,rem,dv,Nat.add_zero] using
      (next_section_deriv hj (n%j) t).const_mul ((-1:ℝ)^(n/j))
  · have id : n%j+1=j := by omega
    rw [if_pos (by omega)] at dv
    have rem : (n+1)%j=0 := by rw [Nat.add_mod,one,id,Nat.mod_self]
    have last : n%j=j-1 := by omega
    have h := (initial_section_deriv hj t).const_mul ((-1:ℝ)^(n/j+1))
    simpa only [signedSection,rem,dv,last,pow_succ,mul_neg,neg_mul,mul_one,neg_neg] using h

private theorem integral_lower {f g : ℝ→ℝ} {v : ℝ} (vp : 0<v)
    (diff : ∀ t,HasDerivAt g (f t) t) (bound : ∀ᶠ t in atTop,v≤f t) :
    Tendsto g atTop atTop := by
  obtain ⟨T,after⟩ := eventually_atTop.mp bound
  let H := fun x ↦ g x - v*x
  have dH (x : ℝ) : HasDerivAt H (f x-v) x := by
    simpa [H,Pi.sub_def] using (diff x).sub ((hasDerivAt_id x).const_mul v)
  have mono : MonotoneOn H (Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (fun x _ ↦ (dH x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (dH x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(dH x).deriv]
    exact sub_nonneg.mpr (after x (interior_subset hx))
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop T,eventually_ge_atTop (T+(b-g T)/v)] with x hx far
  have h0 := mono (show T∈Ici T from (le_rfl : T≤T)) hx hx
  have h1 := (div_le_iff₀ vp).mp (show (b-g T)/v ≤ x-T by linarith)
  dsimp [H] at h0
  linarith

private theorem growth_cycle (F : ℕ→ℝ→ℝ) (der : ∀ n t, HasDerivAt (F (n+1)) (F n t) t)
    {m : ℕ} {v : ℝ} (vp : 0<v) (bound : ∀ᶠ t in atTop,v≤F m t) (k : ℕ) :
    Tendsto (F (m+k+1)) atTop atTop := by
  induction k with
  | zero => simpa using integral_lower vp (der m) bound
  | succ k ih =>
    exact integral_lower (by norm_num : (0:ℝ)<1) (der (m+k+1)) (ih.eventually_ge_atTop 1)

/-- A real antiperiodic cycle of successive primitives cannot have any component
eventually bounded below by a positive constant. The same holds after changing every sign. -/
theorem no_positive_tail {j : ℕ} (jp : 0<j) (F : ℕ→ℝ→ℝ)
    (der : ∀ n t,HasDerivAt (F (n+1)) (F n t) t)
    (flip : ∀ n t,F (n+j) t = -F n t) (m : ℕ) {v : ℝ} (vp : 0<v) :
    ¬ ∀ᶠ t in atTop, v≤F m t := by
  intro hb
  have tg := growth_cycle F der vp hb (j-1)
  rw [show m+(j-1)+1=m+j by omega] at tg
  obtain ⟨t,h1,h2⟩ := (hb.and (tg.eventually_ge_atTop 1)).exists
  rw [flip] at h2
  linarith

#print axioms signed_deriv
#print axioms no_positive_tail
end OrderedPartitions.ReciprocalEdge
