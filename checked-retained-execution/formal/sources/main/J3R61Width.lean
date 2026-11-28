import J3R61Product

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000

/-! Working widths of the literal Horner and accumulated integer product,
including true intermediate products and the common denominator powers. -/
namespace J3R61
open Polynomial V8NativeMessage
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open scoped BigOperators Polynomial Classical

theorem pair_sub_size (a b : Pair ℤ) : (a.minus b).intSize ≤ a.intSize+b.intSize := by
  unfold Pair.intSize Pair.minus
  have ht (x y : ℤ) : (x-y).natAbs ≤ x.natAbs+y.natAbs := by
    rw [sub_eq_add_neg]
    exact (Int.natAbs_add_le _ _).trans (by rw [Int.natAbs_neg])
  exact (Nat.add_le_add (ht a.c b.c) (ht a.d b.d)).trans (by omega)

theorem pair_product_working (a b : Pair ℤ) :
    (a.c*b.c).natAbs ≤ a.intSize*b.intSize ∧
      (a.c*b.d).natAbs ≤ a.intSize*b.intSize ∧
      (a.d*b.c).natAbs ≤ a.intSize*b.intSize ∧
      (a.times b).intSize ≤ a.intSize*b.intSize := by
  have h0 (x : Pair ℤ) : x.c.natAbs ≤ x.intSize := Nat.le_add_right _ _
  have h1 (x : Pair ℤ) : x.d.natAbs ≤ x.intSize := Nat.le_add_left _ _
  simp only [Int.natAbs_mul]
  exact ⟨Nat.mul_le_mul (h0 a) (h0 b),Nat.mul_le_mul (h0 a) (h1 b),
    Nat.mul_le_mul (h1 a) (h0 b),pair_product_size a b⟩

theorem dropped_arity_lte {I : Type*} (arity : I → ℕ) (fs : List I) (k : ℕ) :
    ((fs.drop k).map arity).sum ≤ (fs.map arity).sum := by
  induction k generalizing fs with
  | zero => simp
  | succ k ih =>
    cases fs with
    | nil => simp
    | cons f fs =>
      change ((fs.drop k).map arity).sum ≤ arity f + (fs.map arity).sum
      exact (ih fs).trans (Nat.le_add_left _ _)

noncomputable section
variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

theorem actual_horner_scalar_width (L : CloneTuple F r Q J)
    (bounds : N1.RowBound L hreg R BP) (o : N1.Occ F) (v : Clone W) (k : ℕ) :
    let z := (horner (N1.tInt L)
      ((coeffTape (N1.row L hreg o v) (N1.δ R Q) R).drop k)).value
    let w := hornerCap Q (2^BP) (R+1)
    z.c.natAbs ≤ w ∧ z.d.natAbs ≤ w ∧
      (N1.tInt L*z.c).natAbs ≤ Q*w ∧ (N1.tInt L*z.d).natAbs ≤ Q*w := by
  dsimp only
  let z := (horner (N1.tInt L)
      ((coeffTape (N1.row L hreg o v) (N1.δ R Q) R).drop k)).value
  have hm := actual_coordinate_horner_width L bounds o v k
  have a : z.c.natAbs ≤ hornerCap Q (2^BP) (R+1) := (Nat.le_add_right _ _).trans hm
  have b : z.d.natAbs ≤ hornerCap Q (2^BP) (R+1) := (Nat.le_add_left _ _).trans hm
  exact ⟨a,b,by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (N1.tInt_le L) a,
    by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (N1.tInt_le L) b⟩

theorem actual_factor_operands (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (i : Clone W) (o o' : N1.Occ F) (a b : Bool) :
    let D := N1.δ R Q
    let w := (4*Fintype.card W+1)*hornerCap Q (2^BP) (R+1)
    let read := literalRead L hreg D R i
    let p := (signedAt (D:ℤ) (read o) a).value
    let q := (signedAt (D:ℤ) (read o') b).value
    p.intSize ≤ D+w ∧ q.intSize ≤ D+w ∧
      (p.c*q.c).natAbs ≤ (D+w)^2 ∧ (p.c*q.d).natAbs ≤ (D+w)^2 ∧
      (p.d*q.c).natAbs ≤ (D+w)^2 ∧ (p.times q).intSize ≤ (D+w)^2 ∧
      (Pair.minus (Pair.scalar ((D:ℤ)*(D:ℤ))) (p.times q)).intSize ≤ D^2+(D+w)^2 := by
  dsimp only
  let D := N1.δ R Q
  let w := (4*Fintype.card W+1)*hornerCap Q (2^BP) (R+1)
  let read := literalRead L hreg D R i
  have hw (x : N1.Occ F) : (read x).value.intSize ≤ w := by
    have e : read x = literalRow L hreg R i x := by
      rw [←literalRead_at_printed L hreg R i x,(printedScale_exact R Q).1]
    exact e ▸ literalRow_width L bounds i x
  have hs (x : N1.Occ F) (b : Bool) : (signedAt (D:ℤ) (read x) b).value.intSize ≤ D+w := by
    cases b
    · change (Pair.minus (Pair.scalar (D:ℤ)) (read x).value).intSize ≤ D+w
      exact (pair_sub_size _ _).trans (by
        simpa [Pair.intSize,Pair.scalar] using Nat.add_le_add_left (hw x) D)
    · exact (hw x).trans (Nat.le_add_left _ _)
  let p := (signedAt (D:ℤ) (read o) a).value
  let q := (signedAt (D:ℤ) (read o') b).value
  have hB : p.intSize*q.intSize ≤ (D+w)^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul (hs o a) (hs o' b)
  obtain ⟨hc,h1,h2,h⟩ := pair_product_working p q
  refine ⟨hs o a,hs o' b,hc.trans hB,h1.trans hB,h2.trans hB,h.trans hB,?_⟩
  apply (pair_sub_size _ _).trans
  exact Nat.add_le_add (by simp [Pair.intSize,Pair.scalar,Int.natAbs_mul,pow_two])
    (h.trans hB)

/-- Dyadic bound for every actual integer product suffix and the actual
separate denominator loop; `k` in the denominator ranges over run steps. -/
theorem signed_loop_bit_width (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (i : Clone W) (hi : L.U={i}) (s : W → Bool) (S : Finset (Clause F)) (k : ℕ) :
    let fs := S.toList.drop k
    let u := Nat.clog 2 (N1.A W R Q BP)
    let p := paidProduct (fs.map (factorAt (N1.δ R Q:ℤ)
      (literalRead L hreg (N1.δ R Q) R i) s))
    p.value.intSize ≤ 2^(u*degreeOn S) ∧
      ∀ d ≤ degreeOn S, (powerLoop (N1.δ R Q) d).value ≤ 2^(u*degreeOn S) := by
  dsimp only
  let A := N1.A W R Q BP
  let u := Nat.clog 2 A
  have hA : A ≤ 2^u := Nat.le_pow_clog (by decide) _
  have hδ : N1.δ R Q ≤ A := N1.δ_le_base
  have hu (j : ℕ) (hj : j≤degreeOn S) :
      A^j ≤ 2^(u*degreeOn S) := by
    rw [pow_mul]
    exact (Nat.pow_le_pow_left hA j).trans
      (Nat.pow_le_pow_right (Nat.one_le_two_pow) hj)
  have hfs : ((S.toList.drop k).map N1.arity).sum ≤ degreeOn S := by
    exact (dropped_arity_lte N1.arity S.toList k).trans_eq (Finset.sum_map_toList ..)
  exact ⟨(signed_product_suffix_width L bounds i hi s S k).trans (hu _ hfs),fun d hd=>by
    rw [(powerLoop_exact _ _).1]
    exact (Nat.pow_le_pow_left hδ _).trans (hu d hd)⟩

#print axioms actual_horner_scalar_width
#print axioms pair_product_working
#print axioms actual_factor_operands
#print axioms signed_loop_bit_width

end
end J3R61
