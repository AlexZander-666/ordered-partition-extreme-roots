import OrderedPartitions.ReciprocalEdgeListing

noncomputable section
namespace OrderedPartitions.ReciprocalSector
open Set OrderedPartitions.ReciprocalEdge

theorem NegativeListing.unique {f : ℝ→ℝ} {x y : ℕ→ℝ}
    (A : NegativeListing f x) (B : NegativeListing f y) : x=y := by
  funext n
  induction n with
  | zero =>
    obtain ⟨k,eq⟩ := B.complete (A.negative 0) (A.vanishes 0)
    obtain ⟨l,eq'⟩ := A.complete (B.negative 0) (B.vanishes 0)
    exact le_antisymm (eq ▸ B.decreasing.antitone (Nat.zero_le k))
      (eq' ▸ A.decreasing.antitone (Nat.zero_le l))
  | succ n ih =>
    obtain ⟨k,eq⟩ := B.complete (A.negative (n+1)) (A.vanishes (n+1))
    obtain ⟨l,eq'⟩ := A.complete (B.negative (n+1)) (B.vanishes (n+1))
    have hn : y k<y n := by rw [eq,← ih]; exact A.decreasing (Nat.lt_succ_self n)
    have hn' : x l<x n := by rw [eq',ih]; exact B.decreasing (Nat.lt_succ_self n)
    have nk := B.decreasing.lt_iff_gt.mp hn
    have nl := A.decreasing.lt_iff_gt.mp hn'
    exact le_antisymm (eq ▸ B.decreasing.antitone (show n+1≤k by omega))
      (eq' ▸ A.decreasing.antitone (show n+1≤l by omega))

/-- Negative zeros are listed starting with the rightmost. Under disjointness,
the smaller section has one zero to the right of the first denominator zero
and one between every two denominator zeros. -/
theorem pair_ladder {j : ℕ} (hj : 1≤j) (i k : Fin j) (ik : i<k) {x y : ℕ→ℝ}
    (A : NegativeListing (sectionR j i) x) (B : NegativeListing (sectionR j k) y)
    (far : ∀ b : ℝ, ∃ w, w<b ∧ reciprocalLimit j k w=0)
    (disjoint : ∀ t : ℝ, t<0 → sectionR j k t=0 → sectionR j i t≠0) (n : ℕ) :
    y n < x n ∧ x (n+1)<y n := by
  classical
  have zr (h : ℕ) : sectionR j i (y h)≠0 := disjoint _ (B.negative h) (B.vanishes h)
  have clear0 : ∀ t∈Ioo (y 0) 0, sectionR j k t≠0 := by
    intro t ht ze
    obtain ⟨h,e⟩ := B.complete ht.2 ze
    exact (not_lt_of_ge (B.decreasing.antitone (Nat.zero_le h))) (e ▸ ht.1)
  have clear (l : ℕ) : ∀ t∈Ioo (y (l+1)) (y l), sectionR j k t≠0 := by
    intro t ht ze
    obtain ⟨h,e⟩ := B.complete (ht.2.trans (B.negative l)) ze
    rw [←e] at ht
    have u := B.decreasing.lt_iff_gt.mp ht.1
    have v := B.decreasing.lt_iff_gt.mp ht.2
    omega
  let old := zero_after_last_pole hj i k ik (B.negative 0) (B.vanishes 0) (zr 0) clear0
  let new (l : ℕ) := zero_between_poles hj i k ik (B.decreasing (Nat.lt_succ_self l))
    (B.negative l) (B.vanishes _) (B.vanishes _) (zr _) (zr _) (clear l)
  let z : ℕ→ℝ := fun l ↦ match l with
    | 0 => old.exists.choose
    | l+1 => (new l).exists.choose
  have first : z 0∈Ioo (y 0) 0 ∧ sectionR j i (z 0)=0 := old.exists.choose_spec
  have rest (l : ℕ) : z (l+1)∈Ioo (y (l+1)) (y l) ∧ sectionR j i (z (l+1))=0 :=
    (new l).exists.choose_spec
  have left (l : ℕ) : y l<z l := by cases l with
    | zero => exact first.1.1
    | succ l => exact (rest l).1.1
  have enumerated : NegativeListing (sectionR j i) z := by
    refine ⟨strictAnti_nat_of_succ_lt (fun l ↦ (rest l).1.2.trans (left l)),?_,?_,?_⟩
    · intro l; cases l with
      | zero => exact first.1.2
      | succ l => exact (rest l).1.2.trans (B.negative l)
    · intro l; cases l with
      | zero => exact first.2
      | succ l => exact (rest l).2
    · intro a an za
      obtain ⟨w,wa,rw⟩ := far a
      obtain ⟨l,eq⟩ := B.complete (wa.trans an) (zero_cast.mpr rw)
      have low : y l<a := eq ▸ wa
      clear eq
      induction l with
      | zero => exact ⟨0,old.unique first ⟨⟨low,an⟩,za⟩⟩
      | succ l ih =>
        rcases lt_or_ge (y l) a with prior|later
        · exact ih prior
        · have ne : a≠y l := fun e ↦ zr l (e ▸ za)
          exact ⟨l+1,(new l).unique (rest l) ⟨⟨low,lt_of_le_of_ne later ne⟩,za⟩⟩
  have id := A.unique enumerated
  rw [id]
  exact ⟨left n,(rest n).1.2⟩

#print axioms pair_ladder
end OrderedPartitions.ReciprocalSector
