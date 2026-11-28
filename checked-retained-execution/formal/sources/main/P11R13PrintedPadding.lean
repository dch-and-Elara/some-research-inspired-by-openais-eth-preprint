import P11R12Variance
import J1PPrintedP11
import J1PPrintedSize

namespace P11R13PrintedPadding
open scoped Classical BigOperators
open P11FullPacking J1PPrinted OuterNodePacking
variable {K W : Type*} [LinearOrder K] [Fintype K] [Fintype W] {a : ℕ}

noncomputable def load (f : W → Cell (Fin a) K) (c : Cell (Fin a) K) : ℕ :=
  Nat.card (RealFiber f c)

omit [Fintype K] in
theorem load_eq_filter (f : W → Cell (Fin a) K) (c : Cell (Fin a) K) :
    load f c = ((Finset.univ : Finset W).filter (fun w => f w=c)).card := by
  classical
  unfold load
  let T := (Finset.univ : Finset W).filter (fun w => f w=c)
  have e : RealFiber f c ≃ T := Equiv.subtypeEquivRight (fun w => by simp [T])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem load_mass (f : W → Cell (Fin a) K) :
    (∑ c : Cell (Fin a) K, load f c) = Fintype.card W := by
  classical
  simp only [load_eq_filter]
  symm
  simpa only [Finset.card_univ] using
    (Finset.card_eq_sum_card_fiberwise (f:=f)
      (s:=(Finset.univ : Finset W)) (t:=(Finset.univ : Finset (Cell (Fin a) K)))
        (fun _ _ => Finset.mem_univ _))

noncomputable def printedB (f : W → Cell (Fin a) K) : ℕ :=
  PaddingBounds.blocks ((Finset.univ : Finset (Cell (Fin a) K)).sup (load f)) (2^a)

omit [LinearOrder K] in
theorem cap_of_printedB (f : W → Cell (Fin a) K) :
    ∀ c, Nat.card (RealFiber f c) ≤ printedB f * 2^a := by
  classical
  intro c
  exact padded_real_cap f _ (fun c => Finset.le_sup (f:=load f) (Finset.mem_univ c)) c

/-- Actual occupied and padded slot counts use the very same cell labels
and maximum as the original collision bound, not independent estimates. -/
theorem physical_guards (s d : ℕ) (hK : Fintype.card K=64)
    (f : W → Cell (Fin (stepA (Nat.clog 2 s) d)) K)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (hActive : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < Fintype.card W)
    (hColl : PaddingBounds.collision Finset.univ (load f) (Fintype.card W) ≤
      2*(Fintype.card W:ℝ)*sourceDelta s) :
    let a := stepA (Nat.clog 2 s) d
    let b := printedB f
    (2^a)^2≤b ∧ 0<b ∧ 1<b*2^a ∧ Nat.card (Page a b K)*2^a ≤ 2*Fintype.card W := by
  classical
  let lam := Nat.clog 2 s
  let a := stepA lam d
  let M := Fintype.card W
  let L := stepL lam d
  let D := stepD lam d
  let cells : Finset (Cell (Fin a) K) := Finset.univ
  let b := printedB f
  let P := PaddingBounds.packetCount cells (load f) L
  have hD : cells.card = D := by
    unfold cells D
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, total_cells,hK]
    rfl
  have hM : ∑ c ∈ cells, load f c = M := load_mass f
  have h := printed_padding_slack cells (load f) s M d hU hActive hD hM hColl
  change (M:ℝ) ≤ (P:ℝ)*L ∧ _ at h
  have hm : M≤P*L := by exact_mod_cast h.1
  have hh : P*L≤2*M := by exact_mod_cast h.2.2
  have hPL : P*L=b*L*D := by simp [P,PaddingBounds.packetCount,hD,b,printedB,cells,L,stepL]; ring
  have hb := printed_p11_repetitions s M d b hU hActive (hm.trans_eq hPL)
  have hL : 4≤L := stepL_ge_four lam d hU
  have hPos : 0<b := lt_of_lt_of_le (by positivity : 0<L^2) hb
  have hOne : 1<b*L := by
    have ht := Nat.mul_le_mul_right L (show 1≤b by omega)
    omega
  let mask : MaskFamily a b K := fun _ _ _ => false
  have hPage : Nat.card (Page a b K) = P := by
    rw [total_packets mask,Nat.card_eq_fintype_card (α:=Cell (Fin a) K),← Finset.card_univ]
    rfl
  change L^2≤b ∧ 0<b ∧ 1<b*L ∧ Nat.card (Page a b K)*L ≤ 2*M
  exact ⟨hb,hPos,hOne,by simpa only [hPage] using hh⟩

#print axioms load_eq_filter
#print axioms load_mass
#print axioms cap_of_printedB
#print axioms physical_guards
end P11R13PrintedPadding
