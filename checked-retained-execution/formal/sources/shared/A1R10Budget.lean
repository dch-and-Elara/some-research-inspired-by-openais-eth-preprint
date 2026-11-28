import A1R10UV

/-! Explicit polynomial envelope for the native metered multiplier.
All dimensions are the actual dense tape dimensions; the cost of
generating a coefficient tape from a CNF is not included. -/

namespace A1R10
open AOracleMachineTime

theorem uBudgetGates_poly (e p : ℕ) (hp : 0<p) :
    uBudgetGates e p hp ≤ 424*((e+1)^2*(p+1)^2) := by
  let E := (e+1)^2
  let P := (p+1)^2
  have hP : p+1≤P := by dsimp [P]; nlinarith
  have hE : e*(e+1)≤E := by dsimp [E]; nlinarith
  have he : e≤E := by dsimp [E]; nlinarith
  have hE2 : (e+1)*(2*e+1)≤2*E := by dsimp [E]; nlinarith
  have h1 : 4*(32*P+4*(p+1))≤144*P := by omega
  have h2 : 2*(32*P)+4*(p+1)≤68*P := by omega
  change (e+1)*(2*e+1)*(4*(32*P+4*(p+1)))+
    e*(e+1)*(2*(32*P)+4*(p+1))+e*(2*(32*P)+4*(p+1)) ≤ 424*(E*P)
  calc
    _ ≤ (2*E)*(144*P) + E*(68*P) + E*(68*P) :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hE2 h1) (Nat.mul_le_mul hE h2))
        (Nat.mul_le_mul he h2)
    _ = _ := by ring

theorem uvBudget_poly (e ell p : ℕ) (hp : 0<p) :
    uvBudget e ell p hp ≤ 3432*((ell+1)^2*(e+1)^2*(p+1)^2) := by
  let W := (e+1)^2*(p+1)^2
  let L := (ell+1)^2
  have he : e+1≤(e+1)^2 := by nlinarith
  have hp' : p+1≤(p+1)^2 := by nlinarith
  have hMove : e*p+1≤W :=
    (show e*p+1≤(e+1)*(p+1) by nlinarith).trans (Nat.mul_le_mul he hp')
  have hU : uBudgetGates e p hp≤424*W := uBudgetGates_poly e p hp
  have hGate : 4*(uBudgetGates e p hp+4*(e*p+1))≤1712*W := by omega
  have h1 : (ell+1)*(2*ell+1)≤2*L := by dsimp [L]; nlinarith
  have h2 : 6*ell+2≤8*L := by dsimp [L]; nlinarith
  unfold uvBudget
  calc
    _ ≤ (2*L)*(1712*W)+(8*L)*W :=
      Nat.add_le_add (Nat.mul_le_mul h1 hGate) (Nat.mul_le_mul h2 hMove)
    _ = _ := by dsimp [W,L]; ring

theorem uvMul_native_bit_cost {p : ℕ} (hp : 0<p) {f : List (Word p)} {ell : ℕ}
    (a b : UVBlock f ell) :
    uvRead hp f ell (uvMul hp a b).result = uvRead hp f ell a * uvRead hp f ell b ∧
    (uvMul hp a b).steps ≤ 3432*((ell+1)^2*(f.length+1)^2*(p+1)^2) := by
  obtain ⟨he,hc⟩ := uvMul_exact hp a b
  exact ⟨he,hc.trans (uvBudget_poly f.length ell p hp)⟩

#print axioms uBudgetGates_poly
#print axioms uvBudget_poly
#print axioms uvMul_native_bit_cost
end A1R10
