import P5P3ExactCriterion

/-! Taking the exact active-node minimum in P.2. A zero-order node
contributes no slot and does not constrain the optimum. A profile with
no retained nodes has no positive degree-admissible window. -/
namespace Paper5.P3
open scoped BigOperators

variable {T : Type*} [Fintype T]

def activeNodes (q : T→ℕ) : Finset T := Finset.univ.filter (fun t => 0<q t)

def degreeAdmissible (q : T→ℕ) (d b : ℕ) : Prop :=
  0<b ∧ b≤(∑ t,q t)-d

theorem no_window_of_empty_active (q : T→ℕ) (d b : ℕ)
    (h : activeNodes q = ∅) : ¬degreeAdmissible q d b := by
  intro ⟨hb,hfit⟩
  have hz (t : T) : q t=0 := by
    by_contra hn
    have hh : t∈activeNodes q := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Nat.pos_of_ne_zero hn⟩
    rw [h] at hh
    exact Finset.notMem_empty t hh
  simp only [hz,Finset.sum_const_zero,Nat.zero_sub] at hfit
  omega

noncomputable def largestBound (q : T→ℕ) (d : ℕ) (P loss c : T→ℤ) (p : ℤ)
    (ha : (activeNodes q).Nonempty) : ℤ :=
  min (((∑ t,q t:ℕ):ℤ)-d)
    ((activeNodes q).inf' ha (fun t => 2-↑(q t)+(P t-p+c t)/loss t))

theorem window_cap_p2 (q : T→ℕ) (d b : ℕ) (P loss c : T→ℤ) (p : ℤ)
    (ha : (activeNodes q).Nonempty) (hl : ∀ t,0<q t → 0<loss t) :
    (degreeAdmissible q d b ∧ ∀ t,0<q t → ((b:ℤ)+↑(q t)-2)*loss t ≤ P t-p+c t) ↔
      0<b ∧ (b:ℤ)≤largestBound q d P loss c p ha := by
  rw [pointwise_floor_p2 hl]
  unfold degreeAdmissible largestBound
  have hg (hb : 0<b) : (b≤(∑ t,q t)-d) ↔ ((b:ℤ) ≤ ((∑ t,q t:ℕ):ℤ)-d) := by omega
  have hactive : ∀ t : T, t∈activeNodes q ↔ 0<q t := by
    intro t
    simp [activeNodes]
  constructor
  · rintro ⟨⟨hb,hfit⟩,H⟩
    refine ⟨hb,le_min ((hg hb).1 hfit) ?_⟩
    exact Finset.le_inf' _ _ fun t ht => H t ((hactive t).1 ht)
  · rintro ⟨hb,H⟩
    obtain ⟨hfit,hrow⟩ := le_min_iff.mp H
    refine ⟨⟨hb,(hg hb).2 hfit⟩,fun t ht => ?_⟩
    exact hrow.trans (Finset.inf'_le _ ((hactive t).2 ht))

theorem largest_positive_window (q : T→ℕ) (d : ℕ) (P loss c : T→ℤ) (p : ℤ)
    (ha : (activeNodes q).Nonempty) (hl : ∀ t,0<q t → 0<loss t)
    (hpos : 0<largestBound q d P loss c p ha) :
    IsGreatest {b : ℕ | degreeAdmissible q d b ∧ ∀ t,0<q t →
      ((b:ℤ)+↑(q t)-2)*loss t ≤ P t-p+c t} (largestBound q d P loss c p ha).toNat := by
  let cap := largestBound q d P loss c p ha
  have hb : (cap.toNat:ℤ)=cap := Int.toNat_of_nonneg hpos.le
  constructor
  · apply (window_cap_p2 q d _ P loss c p ha hl).2
    exact ⟨by omega,hb.le⟩
  · intro b hb'
    have h := ((window_cap_p2 q d _ P loss c p ha hl).1 hb').2
    omega

#print axioms no_window_of_empty_active
#print axioms window_cap_p2
#print axioms largest_positive_window
end Paper5.P3
