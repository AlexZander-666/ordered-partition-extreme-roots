import OrderedPartitions.ReciprocalEdgeSectors

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Finset Complex

private def mon (n m : ℕ) (c : ℝ) : ℂ := (n.choose m : ℂ)*(c:ℂ)^m

private theorem mon_step (n m : ℕ) (c : ℝ) :
    mon (n+1) (m+1) c = mon n (m+1) c + (c:ℂ)*mon n m c := by
  simp only [mon, Nat.choose_succ_succ, Nat.cast_add, pow_succ]
  ring

private theorem mon_vanish (n m : ℕ) (c : ℝ) (h : n<m) : mon n m c=0 := by
  simp [mon, Nat.choose_eq_zero_of_lt h]

def binomialSections (d N : ℕ) (c : ℝ) (z : ℂ) (r : Fin (d+1)) : ℂ :=
  ∑ h ∈ range (N+1), (N.choose ((d+1)*h+r.val):ℂ)*(c:ℂ)^((d+1)*h+r.val)*z^h

private theorem pad (d N r : ℕ) (c : ℝ) (z : ℂ) :
    (∑ h ∈ range (N+2), mon N ((d+1)*h+r) c*z^h) =
      ∑ h ∈ range (N+1), mon N ((d+1)*h+r) c*z^h := by
  rw [sum_range_succ, mon_vanish N _ c (by nlinarith [Nat.zero_le (d*N)])]
  ring

theorem binomial_step (d N : ℕ) (c : ℝ) (z : ℂ) :
    binomialSections d (N+1) c z = step z c (binomialSections d N c z) := by
  funext r
  induction r using Fin.cases with
  | zero =>
    simp only [step, Fin.cases_zero, binomialSections, Fin.val_zero, Nat.add_zero, Fin.val_last]
    change (∑ h ∈ range (N+2), mon (N+1) ((d+1)*h) c*z^h) =
      (∑ h ∈ range (N+1), mon N ((d+1)*h) c*z^h) +
        (c:ℂ)*(z*(∑ h ∈ range (N+1), mon N ((d+1)*h+d) c*z^h))
    have padded := pad d N 0 c z
    simp only [Nat.add_zero] at padded
    rw [← padded]
    conv_lhs => rw [sum_range_succ']
    conv_rhs => lhs; rw [sum_range_succ']
    simp only [Nat.mul_zero, pow_zero, mul_one]
    have terms (h : ℕ) :
        mon (N+1) ((d+1)*(h+1)) c*z^(h+1) =
          mon N ((d+1)*(h+1)) c*z^(h+1) +
            (c:ℂ)*(z*(mon N ((d+1)*h+d) c*z^h)) := by
      rw [show (d+1)*(h+1) = ((d+1)*h+d)+1 by ring, mon_step, pow_succ]
      ring
    simp_rw [terms]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have constTerm : mon (N+1) 0 c = mon N 0 c := by simp [mon]
    rw [constTerm]
    ring
  | succ i =>
    simp only [step, Fin.cases_succ, binomialSections, Fin.val_succ, Fin.val_castSucc]
    change (∑ h ∈ range (N+2), mon (N+1) ((d+1)*h+(i.val+1)) c*z^h) =
      (∑ h ∈ range (N+1), mon N ((d+1)*h+(i.val+1)) c*z^h) +
        (c:ℂ)*(∑ h ∈ range (N+1), mon N ((d+1)*h+i.val) c*z^h)
    rw [← pad d N (i.val+1) c z, ← pad d N i.val c z, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro h _
    rw [← Nat.add_assoc, mon_step]
    ring

private theorem initial_chain (d : ℕ) {z : ℂ} (up : 0≤z.im) (c : ℝ) :
    AreaChain z (binomialSections d 0 c z) := by
  intro i k ik
  by_cases eq : i=k
  · subst k
    exact sector_self up _
  have kpos : 0 < k.val := by
    have strict : i < k := lt_of_le_of_ne ik eq
    change i.val < k.val at strict
    omega
  have van : binomialSections d 0 c z k=0 := by
    simp [binomialSections, Nat.choose_eq_zero_of_lt kpos]
  rw [van]
  simp [Sector]

theorem binomial_chain {d : ℕ} (N : ℕ) {z : ℂ} (up : 0≤z.im) {c : ℝ} (hc : 0≤c) :
    AreaChain z (binomialSections d N c z) := by
  induction N with
  | zero => exact initial_chain d up c
  | succ N ih => rw [binomial_step]; exact step_preserves up hc ih

#print axioms binomial_step
#print axioms binomial_chain
end OrderedPartitions.ReciprocalSector
