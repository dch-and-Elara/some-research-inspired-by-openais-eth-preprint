import J6IntegerDecode
import J6Mesh

/-! Integer factor removal and exact signed odd-root decoding for every
printed address. This is conditional on physical residue identification,
not a correctness assertion about the Appendix D recursive compiler. -/
namespace J6IntegerDecode
open scoped Polynomial

variable {P T : Type*} [Fintype P] [DecidableEq P] [Fintype T] [DecidableEq T]

omit [DecidableEq T] in
theorem layer_at_printed_address
    (A B : (P → Bool) → Bool) (a q p N : ℕ) (i : J6Recovery.Addr a)
    (n d : ℤ) (k : T → ℕ) (z : ZMod (2^p))
    (hd : 0 < d) (hn : n ≤ 0)
    (hnode : (n:ℚ)/d = J6Mesh.point a i)
    (hreg : let e := J6Recovery.exp a i
      let u := J6IntegerLayers.factor (P:=P) n d (J6Mesh.index a i) q k
      (d : ZMod (2^p))^N * z =
        ((u*(J6IntegerLayers.oldLayer A B n d)^e : ℤ) : ZMod (2^p)))
    (fits : let e := J6Recovery.exp a i
      let u := J6IntegerLayers.factor (P:=P) n d (J6Mesh.index a i) q k
      2*|u*(J6IntegerLayers.oldLayer A B n d)^e| < (↑((2:ℕ)^p) : ℤ)) :
    let u := J6IntegerLayers.factor (P:=P) n d (J6Mesh.index a i) q k
    let ret := integerDecode p (J6Recovery.exp a i) N d u z
    (ret.1 : ℚ)/(d:ℚ)^Fintype.card P =
      (LayerRecovery.layerPolynomial (J6IntegerLayers.oldWeight A)
        (J6IntegerLayers.oldWeight B)).eval (J6Mesh.point a i) ∧ ret.2 = p := by
  dsimp only
  have hu := (J6IntegerLayers.public_pos (P:=P) n d (J6Mesh.index a i) q k hd hn).ne'
  rw [residue_root p _ N d _ _ z hu (J6Recovery.odd_exp a i) hreg fits]
  refine ⟨?_,rfl⟩
  rw [J6IntegerLayers.oldLayer_cast A B n d hd.ne',hnode,mul_div_cancel_left₀]
  exact pow_ne_zero _ (by exact_mod_cast hd.ne')

#print axioms layer_at_printed_address
end J6IntegerDecode