import J6R48BitCostLoaderDelta

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000

/-! Honest boundary of a supplied-loader interface: validating which bits
are returned does not constrain the meter charge. A proof-side padding
preserves every literal mask and the actual centre result, yet changes
the native execution meter by exactly the number of repeated loads. -/
namespace J6R48BitCost
open A1R10 A1R12 AOracleMachineTime J6R22Active J6R24MeteredRecursion

variable {p ell k n : ℕ} {Mode : Type*}

def padMasks (I : SiteTape p ell k n Mode) (extra : ℕ) : SiteTape p ell k n Mode :=
  {I with masks:=fun z=>padCost (I.masks z) extra}

theorem mask_bits_unchanged (I : SiteTape p ell k n Mode) (extra : ℕ) (z : Fin n) :
    ((padMasks I extra).masks z).result=(I.masks z).result := rfl

theorem single_padded_load_delta (I : SiteTape p ell k n Mode) (extra : ℕ) (z : Fin n) :
    Delta ((padMasks I extra).nodeM z) (I.nodeM z) extra := by
  refine ⟨rfl,?_⟩
  simp only [padMasks,SiteTape.nodeM,padCost]
  omega

theorem native_probe_loader_boundary (I : SiteTape p ell k n Mode) (a : ℕ) (t : ℤ) (extra : ℕ) :
    Delta ((padMasks I extra).run a t) (I.run a t) (n*(n*extra)) := by
  let J := padMasks I extra
  let N := I.normM a t
  let x := interpPrefix I.hp I.nonempty I.he I.hk J.nodeM I.groupedM
  let y := interpPrefix I.hp I.nonempty I.he I.hk I.nodeM I.groupedM
  let Q := divideJet I.hp I.nonempty I.he I.hk N.result
  have h : Delta x y (n*(n*extra)) :=
    interpolation_load_delta I.hp I.nonempty I.he I.hk J.nodeM I.nodeM I.groupedM extra
      (single_padded_load_delta I extra)
  refine ⟨?_,?_⟩
  · change (Q x.result).result=(Q y.result).result
    rw [h.value]
  · change N.steps+x.steps+(Q x.result).steps+4=
      N.steps+y.steps+(Q y.result).steps+4+n*(n*extra)
    rw [h.value,h.fee]
    omega

theorem valid_same_probe_meter_can_exceed (I : SiteTape p ell k n Mode) (a : ℕ) (t : ℤ)
    (hn : 0<n) (budget : ℕ) :
    (∀ z,((padMasks I budget).masks z).result=(I.masks z).result) ∧
      ((padMasks I budget).run a t).result=(I.run a t).result ∧
      budget≤((padMasks I budget).run a t).steps := by
  obtain ⟨value,cost⟩ := native_probe_loader_boundary I a t budget
  refine ⟨mask_bits_unchanged I budget,value,?_⟩
  rw [cost]
  have h : budget≤n*budget := Nat.le_mul_of_pos_left _ hn
  exact (h.trans (Nat.le_mul_of_pos_left _ hn)).trans (Nat.le_add_left _ _)

#print axioms mask_bits_unchanged
#print axioms single_padded_load_delta
#print axioms native_probe_loader_boundary
#print axioms valid_same_probe_meter_can_exceed
end J6R48BitCost

