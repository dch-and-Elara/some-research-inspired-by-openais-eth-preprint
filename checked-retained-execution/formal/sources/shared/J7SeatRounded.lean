import J7SeatCertificate

/-! # The source's exact maximum-load rounding, not optional excess padding. -/
open scoped BigOperators Classical

namespace J7SeatRounded
open P11FullPacking J7SeatPacking J7SeatSource J7SeatCertificate
open J7SourceLabels J7FullWordCells J7FullWordAssembly

noncomputable section
set_option maxHeartbeats 1600000

theorem ceilCopies_le {L n b : ℕ} (hL : 0 < L) (hcap : n ≤ b*L) :
    ceilCopies L n ≤ b := by
  by_contra! hn
  have hf := (rounded_capacity L n hL).2
  have hbig := Nat.mul_le_mul_right L (Nat.succ_le_of_lt hn)
  rw [Nat.succ_mul] at hbig
  omega

def realMaximum {W C : Type*} [Fintype W] [Fintype C] (label : W → C) : ℕ :=
  Finset.univ.sup (fun c => Nat.card {w // label w = c})

theorem real_maximum_point {W C : Type*} [Fintype W] [Fintype C]
    (label : W → C) (c : C) : Nat.card {w // label w = c} ≤ realMaximum label :=
  Finset.le_sup (f := fun x => Nat.card {w // label w = x}) (Finset.mem_univ c)

theorem real_maximum_le {W C : Type*} [Fintype W] [Fintype C]
    (label : W → C) (b : ℕ) (cap : ∀ c, Nat.card {w // label w = c} ≤ b) :
    realMaximum label ≤ b := Finset.sup_le fun c _ => cap c

/-- Physical endpoint fillers at an upper packed size already provide
an inheritance certificate at the source's exact rounded maximum, with
all endpoint seats still filled. -/
theorem seat_at_rounded_max {A Pair Row Col W : Type*} [LinearOrder A] [Fintype A]
    [Fintype Pair] [Fintype W] {t b : ℕ}
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin t → A) Pair Row Col) (hz : ∀ d, 0 < weight d (z d))
    (cap : ∀ c, Nat.card {w // wordLabel row col z w = c} ≤ b*2^(t+1))
    (j : Wire Pair W ↪ Physical (t+1) b A)
    (word : ∀ w, physicalCell (balancedMask (t+1) b) (j w) = wordLabel row col z w)
    (fillAll : ∀ s, isEnd s → ∃ w, j w = s)
    (hR : Set.InjOn (rowNode row) {w | isEnd (j w)})
    (hC : Set.InjOn (colNode col) {w | isEnd (j w)})
    (hP : ∀ p : Pin Pair, ¬isEnd (j (pinEmbed Pair W p))) :
    let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z))
    b' ≤ b ∧ ∃ j' : Wire Pair W ↪ Physical (t+1) b' A,
      (∀ w, physicalCell (balancedMask (t+1) b') (j' w) = wordLabel row col z w) ∧
      (∀ s, isEnd s → ∃ w, j' w = s) ∧
      (Set.InjOn (rowNode row) {w | isEnd (j' w)}) ∧
      (Set.InjOn (colNode col) {w | isEnd (j' w)}) ∧
      (∀ p : Pin Pair, ¬isEnd (j' (pinEmbed Pair W p)) ∧
        ((physicalCell (balancedMask (t+1) b') (j' (pinEmbed Pair W p))) 0).1 ≠
          ((physicalCell (balancedMask (t+1) b') (j' (pinEmbed Pair W p))) 0).2) := by
  classical
  dsimp only
  let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z))
  let selected : Set (Wire Pair W) := {w | isEnd (j w)}
  have hsize : b' ≤ b := ceilCopies_le (by positivity) (real_maximum_le _ _ cap)
  refine ⟨hsize,?_⟩
  have hFill (c : Cell (Fin (t+1)) A) :
      2*b ≤ Nat.card {w : {w // wordLabel row col z w = c} // w.val ∈ selected} := by
    let fromEnd (s : EndFiber (b:=b) c) := (fillAll s.val.val s.prop).choose
    have hs (s : EndFiber (b:=b) c) : j (fromEnd s) = s.val.val :=
      (fillAll s.val.val s.prop).choose_spec
    let f (s : EndFiber (b:=b) c) :
        {w : {w // wordLabel row col z w = c} // w.val ∈ selected} :=
      ⟨⟨fromEnd s, (word _).symm.trans ((congrArg (physicalCell (balancedMask (t+1) b)) (hs s)).trans s.val.prop)⟩,
        by
          change isEnd (j (fromEnd s))
          rw [hs s]
          exact s.prop⟩
    have hf : Function.Injective f := by
      intro s u he
      have hh : fromEnd s = fromEnd u := congrArg (fun x => x.val.val) he
      apply Subtype.ext
      apply Subtype.ext
      exact (hs s).symm.trans ((congrArg j hh).trans (hs u))
    rw [← card_ends (b:=b) (by omega : 0 < t+1) c]
    exact Nat.card_le_card_of_injective f hf
  have hNon : ∀ w ∈ selected, nonpin col w := by
    intro w hw
    rw [pin_nonpin_complement]
    intro hm
    obtain ⟨p,_,rfl⟩ := Finset.mem_map.mp hm
    exact hP p hw
  obtain ⟨j',hj,_,he,hr,hc,hp⟩ := seat_source row col z hz selected hR hC hNon
    (padded_real_cap (wordLabel row col z) _ (real_maximum_point _))
    (fun c => (Nat.mul_le_mul_left 2 hsize).trans (hFill c))
  exact ⟨j',hj,he,hr,hc,hp⟩

#print axioms ceilCopies_le
#print axioms real_maximum_point
#print axioms seat_at_rounded_max

end
end J7SeatRounded
