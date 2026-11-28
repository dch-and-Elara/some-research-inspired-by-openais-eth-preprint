import J3R61Normalize
import J3R61Width

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000

/-! Source arithmetic budget on the actual selected menu. Counts the
cell programs whose outputs form the matrix consumed by R60. -/
namespace J3R61
open V8NativeMessage J3R60 J3R38LiteralSingleton
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open scoped BigOperators Classical
noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

def perScore (R Q n : ℕ) : ℕ := (R-1)+Q+1+6+rowOps R (4*n)
def perNormalizedRow (R Q n : ℕ) : ℕ :=
  (R-1)+Q+1+3+(rowOps R (4*n)+10)*(12*n)+((R-1)+Q+1+3+rowOps R (4*n)+3)*n+4

def assemblyOps (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (R : ℕ) (A : Finset (Address W Q)) (heard : {a // a∈A} → Pair ℚ) : ℕ :=
  ∑ a : {a // a∈A},
    let L := literalTuple P R hJ Prow a.val
    (runNormalize L hreg R a.val.2 (heard a)).ops+
      ∑ v : W, (runGraph L hreg R a.val.2 v).ops

theorem selected_menu_arithmetic (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (R : ℕ) (A : Finset (Address W Q)) (heard : {a // a∈A} → Pair ℚ) :
    assemblyOps P Prow hJ R A heard ≤
      A.card*(perNormalizedRow R Q (Fintype.card W)+Fintype.card W*perScore R Q (Fintype.card W)) := by
  unfold assemblyOps
  let Z := perNormalizedRow R Q (Fintype.card W)+Fintype.card W*perScore R Q (Fintype.card W)
  calc
    _ ≤ ∑ _a : {a // a∈A}, Z := by
      apply Finset.sum_le_sum
      intro a _
      let L := literalTuple P R hJ Prow a.val
      change (runNormalize L hreg R a.val.2 (heard a)).ops+
        ∑ v : W,(runGraph L hreg R a.val.2 v).ops ≤ Z
      have hn : (runNormalize L hreg R a.val.2 (heard a)).ops ≤ perNormalizedRow R Q (Fintype.card W) :=
        runNormalize_ops L hreg R a.val.2 (heard a)
      have hs (v : W) : (runGraph L hreg R a.val.2 v).ops = perScore R Q (Fintype.card W) :=
        runGraph_arithmetic L hreg R a.val.2 v
      apply (Nat.add_le_add_right hn _).trans
      simp [Z,hs]
    _ = _ := by simp [Z]

theorem normalized_score_working_height (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q)
    (a : Address W Q) (v : W) (s : W → Bool)
    (h : N1.RowBound (literalTuple P R hJ Prow a) hreg R BP) :
    let L := literalTuple P R hJ Prow a
    let p := (runPin L hreg R a.2 v).value
    let B := publicHeight W R Q BP
    inputHeight (B+1) (1-p.c) ∧ inputHeight (B+(B+1)) (p.c*(1-p.c)) ∧
      inputHeight (B+(B+(B+1))) (runGraph L hreg R a.2 v).value := by
  obtain ⟨_,_,_,_,ht,hd⟩ := original_J3_primitives_height P Prow hJ hr hR hfit a s h
  dsimp only
  have hp : (runPin (literalTuple P R hJ Prow a) hreg R a.2 v).value =
    ⟨pinConstant hreg Prow a.1 v,pinDerivative hreg Prow a v⟩ :=
      runPin_exact P Prow hJ a h v
  simp only [runGraph,hp]
  have q := height_one_sub (ht v)
  have z := height_mul (ht v) q
  exact ⟨q,z,height_div (hd v) z⟩

theorem offset_suffix_width {I : Type*} {B : ℕ} (p : I → Paid (Pair ℚ)) (vs : List I)
    (hp : ∀ v,inputHeight B (p v).value.c ∧ inputHeight B (p v).value.d) :
    inputHeight ((B+(B+1)+1)*vs.length) (offsets p vs).value := by
  induction vs with
  | nil => simp [offsets,inputHeight]
  | cons v vs ih =>
    change inputHeight ((B+(B+1)+1)*(vs.length+1))
      ((p v).value.d/(1-(p v).value.c)+(offsets p vs).value)
    have hv := height_div (hp v).2 (height_one_sub (hp v).1)
    have h := height_add hv ih
    convert h using 1
    rw [Nat.mul_add,Nat.mul_one]
    omega

theorem original_normalizer_working_width (P : Seating F Copy r Q hreg)
    (Prow : Replacement F) (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q)
    (a : Address W Q) (s : W → Bool)
    (h : N1.RowBound (literalTuple P R hJ Prow a) hreg R BP) :
    let L := literalTuple P R hJ Prow a
    let heard := jetTwo (rawJet P R hJ Prow a s)
    let B := publicHeight W R Q BP
    inputHeight (B+B) (heard.d/heard.c) ∧
      inputHeight (B+B) ((runPublic L hreg R a.2).value.d/(runPublic L hreg R a.2).value.c) ∧
      (∀ k, inputHeight ((B+(B+1)+1)*Fintype.card W)
        (offsets (runPin L hreg R a.2) ((Finset.univ : Finset W).toList.drop k)).value) ∧
      inputHeight (normHeight B (Fintype.card W)) (runNormalize L hreg R a.2 heard).value := by
  dsimp only
  let L := literalTuple P R hJ Prow a
  let B := publicHeight W R Q BP
  have hn := original_J3_primitives_height P Prow hJ hr hR hfit a s h
  obtain ⟨h0,h1,hb0,hb1,ht,hd⟩ := hn
  refine ⟨height_div h1 h0,?_,?_,?_⟩
  · rw [runPublic_exact L h hJ a.2 rfl]
    change inputHeight (B+B) ((backgroundPoly L hreg).coeff 1/(backgroundPoly L hreg).coeff 0)
    rw [public_constant_is_Bt hreg L]
    exact height_div hb1 hb0
  · intro k
    let vs := (Finset.univ : Finset W).toList.drop k
    have hw : vs.length ≤ Fintype.card W := by
      simpa only [vs,List.length_drop,Finset.length_toList,Finset.card_univ] using
        Nat.sub_le (Fintype.card W) k
    have ha := offset_suffix_width (B:=B) (runPin L hreg R a.2) vs (fun v => by
      rw [runPin_exact P Prow hJ a h v]
      exact ⟨ht v,hd v⟩)
    exact inputHeight_mono (Nat.mul_le_mul_left _ hw) ha
  · rw [runNormalize_original P Prow hJ a h]
    exact (normalized_equation_height _ _ _ _ _ _ h0 h1 hb0 hb1 ht hd).2

#print axioms selected_menu_arithmetic
#print axioms normalized_score_working_height
#print axioms offset_suffix_width
#print axioms original_normalizer_working_width

end
end J3R61
