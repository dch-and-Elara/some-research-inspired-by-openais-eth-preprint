import J1PPrintedMain

set_option autoImplicit false
set_option warningAsError true

/-! A conservative finite sufficient input size for the original J1
printed guards. It certifies the eventual quantifier for every fixed beta,
without altering the definition of either Q or r. -/
namespace J1R43Literal
open J1PPrinted J1PhysicalPrinted

def sizeFloor (beta : ℕ) : ℕ :=
  2 ^ (2 ^ (2*(max 32 (beta+2)+1)))

theorem printed_guards_eventually (N beta : ℕ) (hN : sizeFloor beta≤N) :
    0<N ∧ 32≤mainScaleIndex (Nat.clog 2 (4*N)) ∧
      beta+3≤mainScaleIndex (Nat.clog 2 (4*N))+1 := by
  let u := 2*(max 32 (beta+2)+1)
  let lambda := Nat.clog 2 (4*N)
  have hp : 0<sizeFloor beta := by unfold sizeFloor; positivity
  have hn : 0<N := hp.trans_le hN
  have hval : 2^(2^u)≤4*N := hN.trans (by omega)
  have a := Nat.clog_mono_right 2 hval
  rw [Nat.clog_pow 2 (2^u) (by decide)] at a
  have b := Nat.clog_mono_right 2 a
  rw [Nat.clog_pow 2 u (by decide)] at b
  change u≤sourceNu lambda at b
  change 0<N ∧ 32≤sourceNu lambda/2-1 ∧ beta+3≤sourceNu lambda/2-1+1
  have hβ : beta+2≤max 32 (beta+2) := le_max_right _ _
  have h32 : 32≤max 32 (beta+2) := le_max_left _ _
  dsimp [u] at b
  omega

#print axioms printed_guards_eventually

end J1R43Literal