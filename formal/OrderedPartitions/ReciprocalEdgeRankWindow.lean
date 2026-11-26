import OrderedPartitions.ReciprocalEdgeWindowOrder
import OrderedPartitions.HardRodAffineReadout
import OrderedPartitions.HardRodStableDegree

/-! The fixed-prefix theorem for the actual pair of ordered-partition ranks n<m≤n+j. -/
noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Filter Polynomial OrderedPartitions.ReciprocalEdge
open scoped Topology

/-- Direct statement about the actual complex polynomial of rank n. -/
structure ExtremeRoots {k : ℕ} (p : ℝ[X]) (v : Fin k → ℝ) : Prop where
  ordered : StrictMono v
  negative : ∀ i, v i<0
  zero : ∀ i, p.eval₂ Complex.ofRealHom (v i:ℂ)=0
  simple : ∀ i, deriv (p.eval₂ Complex.ofRealHom) (v i:ℂ)≠0
  modulus : ∀ w : ℂ, p.eval₂ Complex.ofRealHom w=0 → (∀ i, w≠(v i:ℂ)) →
    ∀ i, ‖w‖<‖(v i:ℂ)‖

theorem extreme_at_rank {n j k : ℕ} {ρ ε : ℝ} {c v : Fin k → ℝ}
    (h : OriginalOuterPrefix j (n%j) (n/j) ρ ε c v) : ExtremeRoots (row n j) v := by
  have identity := Nat.div_add_mod n j
  refine ⟨h.ordered,h.negative,?_,?_,?_⟩
  · simpa only [originalValue,identity] using h.zero
  · have certificate := h.simple
    change ∀ i, deriv (fun z : ℂ ↦ (row (j*(n/j)+n%j) j).eval₂ Complex.ofRealHom z) (v i:ℂ) ≠ 0 at certificate
    rw [identity] at certificate
    exact certificate
  · intro w root other i
    exact (h.remaining w (by simpa only [originalValue,identity] using root) other).trans (h.selected i)

theorem rank_degree {n j : ℕ} (hj : 2≤j) (jn : j≤n) : (row n j).natDegree=n/j := by
  have jp : 0<j := by omega
  have positive : 1≤n/j := (Nat.le_div_iff_mul_le jp).mpr (by simpa using jn)
  have cap : n<(n/j+1)*j := (Nat.div_lt_iff_lt_mul jp).mp (Nat.lt_succ_self _)
  exact (RootTracking.original_window_degree hj cap).trans
    (RootTracking.window_shape hj positive (le_refl _) (Nat.div_mul_le_self _ _) cap).1

/-- At every large enough rank n select its K most distant roots. All matches in
n<m≤n+j alternate, old first at equal degree, new first at the unit degree rise. -/
theorem original_rank_window {j : ℕ} (hj : 2≤j) (k : ℕ) :
    ∃ v : ℕ → Fin k → ℝ, ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n<m → m≤n+j →
      ExtremeRoots (row n j) (v n) ∧ ExtremeRoots (row m j) (v m) ∧
      (row n j).natDegree=n/j ∧ (row m j).natDegree=m/j ∧
      ((n/j=m/j ∧ AlternatingPrefix (v n) (v m)) ∨
       (m/j=n/j+1 ∧ AlternatingPrefix (v m) (v n))) := by
  have jp : 0<j := by omega
  obtain ⟨L,_,rows⟩ := all_ordered_extremes hj
  obtain ⟨t,h,tests⟩ := rows k
  let r (n : ℕ) : Fin j := ⟨n%j,Nat.mod_lt _ jp⟩
  let v (n : ℕ) := t (n/j) (r n)
  obtain ⟨B,big⟩ := eventually_atTop.mp ((tests 2).and (h.certified 1 one_pos))
  refine ⟨v,eventually_atTop.mpr ⟨max j (B*j),?_⟩⟩
  intro n hn m nm span
  have jn : j≤n := (le_max_left _ _).trans hn
  have bd : B≤n/j := (Nat.le_div_iff_mul_le jp).mpr ((le_max_right _ _).trans hn)
  have order : n/j≤m/j := Nat.div_le_div_right nm.le
  have cap : m/j≤n/j+1 := (Nat.div_le_div_right span).trans_eq (Nat.add_div_right n jp)
  have nr := (big _ bd).2 (r n)
  have mr := (big _ (bd.trans order)).2 (r m)
  refine ⟨extreme_at_rank nr,extreme_at_rank mr,rank_degree hj jn,
    rank_degree hj (jn.trans nm.le),?_⟩
  have en := Nat.div_add_mod n j
  have em := Nat.div_add_mod m j
  by_cases eq : n/j=m/j
  · have lt : r n<r m := by
      change n%j<m%j
      rw [← eq] at em
      omega
    have test := (big _ bd).1 (0:Fin 2) (0:Fin 2) (r n) (r m) (Or.inl lt)
    exact Or.inl ⟨eq,by simpa only [Fin.val_zero,Nat.add_zero,v,←eq] using test⟩
  · have succ : m/j=n/j+1 := by omega
    have le : r m≤r n := by
      change m%j≤n%j
      rw [succ,Nat.mul_add,Nat.mul_one] at em
      omega
    have ord : r m<r n ∨ (r m=r n ∧ (0:Fin 2)<1) := by
      rcases le.lt_or_eq with sub|same
      · exact Or.inl sub
      · exact Or.inr ⟨same,by decide⟩
    have test := (big _ bd).1 (1:Fin 2) (0:Fin 2) (r m) (r n) ord
    exact Or.inr ⟨succ,by simpa only [v,succ,Fin.val_zero,Fin.val_one,Nat.add_zero] using test⟩

#print axioms rank_degree
#print axioms original_rank_window
end OrderedPartitions.ReciprocalSector
