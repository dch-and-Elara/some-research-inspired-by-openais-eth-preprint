import J3R61Native

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5300000

/-! Execute the actual public normalizer on the two real observed values,
then pass the actual computed graph system to the already proved solver.
The program takes received coefficients, not the secret sign word. -/
namespace J3R61
open Polynomial V8NativeMessage J3R59 J3R60 J3R38LiteralSingleton
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open scoped Polynomial BigOperators Classical

def offsets {I : Type*} (p : I → Paid (Pair ℚ)) : List I → Paid ℚ
  | [] => ⟨0,0⟩
  | v :: vs =>
    let row := p v
    let s := offsets p vs
    ⟨row.value.d/(1-row.value.c)+s.value,row.ops+s.ops+3⟩

theorem offsets_value {I : Type*} (p : I → Paid (Pair ℚ)) (vs : List I) :
    (offsets p vs).value = (vs.map (fun v => (p v).value.d/(1-(p v).value.c))).sum := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [offsets,List.map_cons,List.sum_cons,ih]

theorem offsets_ops {I : Type*} (p : I → Paid (Pair ℚ)) (vs : List I) (n : ℕ)
    (h : ∀ v,(p v).ops=n) :
    (offsets p vs).ops=(n+3)*vs.length := by
  induction vs with
  | nil => simp [offsets]
  | cons v vs ih =>
    simp only [offsets,h,ih,List.length_cons,Nat.mul_succ]
    omega

noncomputable section
variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

def runNormalize (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) (heard : Pair ℚ) : Paid ℚ :=
  let pub := runPublic L hreg R i
  let r := offsets (runPin L hreg R i) (Finset.univ : Finset W).toList
  ⟨heard.d/heard.c - pub.value.d/pub.value.c + r.value, pub.ops+r.ops+4⟩

theorem runNormalize_original (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (a : Address W Q)
    (hb : N1.RowBound (literalTuple P R hJ Prow a) hreg R BP) (heard : Jet J) :
    (runNormalize (literalTuple P R hJ Prow a) hreg R a.2 (jetTwo heard)).value =
      normalize P R hJ Prow a heard := by
  let L := literalTuple P R hJ Prow a
  change (jetTwo heard).d/(jetTwo heard).c -
    (runPublic L hreg R a.2).value.d/(runPublic L hreg R a.2).value.c +
    (offsets (runPin L hreg R a.2) (Finset.univ : Finset W).toList).value = _
  have hoff : (offsets (runPin L hreg R a.2) (Finset.univ : Finset W).toList).value =
      ∑ v, pinDerivative hreg Prow a v / (1-pinConstant hreg Prow a.1 v) := by
    rw [offsets_value,Finset.sum_map_toList]
    apply Finset.sum_congr rfl
    intro v _
    have hp : (runPin L hreg R a.2 v).value =
        ⟨pinConstant hreg Prow a.1 v,pinDerivative hreg Prow a v⟩ :=
      runPin_exact P Prow hJ a hb v
    rw [hp]
  rw [runPublic_exact L hb hJ a.2 rfl,hoff]
  simp only [capture,jetTwo,J3R38LiteralSingleton.normalize,public_constant_is_Bt hreg L]
  rfl

theorem runNormalize_ops (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) (heard : Pair ℚ) :
    (runNormalize L hreg R i heard).ops ≤
      (R-1)+Q+1+3+(rowOps R (4*Fintype.card W)+10)*(12*Fintype.card W)
      + (((R-1)+Q+1+3+rowOps R (4*Fintype.card W))+3)*Fintype.card W+4 := by
  have ho := offsets_ops (runPin L hreg R i) (Finset.univ : Finset W).toList
    _ (fun v=>runPin_ops L hreg R i v)
  simp only [Finset.length_toList,Finset.card_univ] at ho
  change (runPublic L hreg R i).ops+
    (offsets (runPin L hreg R i) (Finset.univ : Finset W).toList).ops+4 ≤ _
  rw [ho]
  exact Nat.add_le_add_right (Nat.add_le_add_right (runPublic_ops L hreg R i) _) _

def runCodedSolve (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (R : ℕ) (Aset : Finset (Address W Q)) (rows : List {a // a∈Aset})
    (cols : Fin (Fintype.card W) ≃ W) (heard : {a // a∈Aset} → Pair ℚ) :
    Option (Fin (Fintype.card W) → ℚ) × OpLedger :=
  measuredScaled rows
    (fun a j => (runGraph (literalTuple P R hJ Prow a.val) hreg R a.val.2 (cols j)).value)
    (fun a => (runNormalize (literalTuple P R hJ Prow a.val) hreg R a.val.2 (heard a)).value)

/-- The executed Horner/product graph system is the literal R60 table. -/
theorem runCodedSolve_same_system (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (Aset : Finset (Address W Q)) (rows : List {a // a∈Aset})
    (cols : Fin (Fintype.card W) ≃ W)
    (hb : ∀ a ∈ Aset, N1.RowBound (literalTuple P R hJ Prow a) hreg R BP)
    (heard : {a // a∈Aset} → Jet J) :
    runCodedSolve P Prow hJ R Aset rows cols (fun a => jetTwo (heard a)) =
      measuredScaled rows (fun (a : {a // a∈Aset}) j => graphEntry hreg Prow a.val (cols j))
        (fun a => normalize P R hJ Prow a.val (heard a)) := by
  unfold runCodedSolve
  congr 1
  · funext a j
    exact runGraph_original P Prow hJ a.val (hb a.val a.property) (cols j)
  · funext a
    exact runNormalize_original P Prow hJ a.val (hb a.val a.property) (heard a)

theorem runCodedSolve_recovers_original (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (hr : 2 ≤ r) (hR : 1 ≤ R) (hfit : 6*R≤Q)
    (Aset : Finset (Address W Q)) (ok : ∀ a∈Aset,Admissible hreg Prow a.1)
    (hRank : (graphMatrix hreg Prow Aset).rank=Fintype.card W)
    (rows : List {a // a∈Aset}) (hn : rows.Nodup) (allRows : ∀ a,a∈rows)
    (cols : Fin (Fintype.card W) ≃ W)
    (hb : ∀ a ∈ Aset, N1.RowBound (literalTuple P R hJ Prow a) hreg R BP) (s : W → Bool) :
    (runCodedSolve P Prow hJ R Aset rows cols (fun a => jetTwo (rawJet P R hJ Prow a.val s))).1 =
      some (fun j => JointContraction.bitScalar ℚ (s (cols j))) := by
  rw [runCodedSolve_same_system P Prow hJ Aset rows cols hb]
  exact (original_J3_actual_budget P Prow hJ hr hR hfit Aset ok hRank rows hn allRows cols s).2.2.1

#print axioms offsets_ops
#print axioms runNormalize_original
#print axioms runNormalize_ops
#print axioms runCodedSolve_same_system
#print axioms runCodedSolve_recovers_original

end
end J3R61
