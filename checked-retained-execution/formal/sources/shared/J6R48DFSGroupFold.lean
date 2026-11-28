import J6R48DFSModeDrain
import J6R22ActiveNativeGroup
import J6R21LeafWidth

/-! One probe: a left accumulator for the product across the 64 stock
group occurrences, and an outside accumulator for the sum across the
actual mode cursor. The data terms and arithmetic widths are real
UV words. A child's meter is consumed once per occurrence. -/
namespace J6R48DFS
open scoped BigOperators
open AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active J6R21Leaf

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3600000

variable {e p ell q : ℕ} {fw : List (A1R10.Word p)}

def productCursor {A : Type*} (hp : 0<p) (read : A→Meter (UVBlock fw ell)) :
    List A→UVBlock fw ell→ℕ→Meter (UVBlock fw ell)
  | [],u,fee => ⟨u,fee⟩
  | a::as,u,fee =>
    let x := read a
    let y := mulM hp ⟨u,0⟩ x
    productCursor hp read as y.result (fee+y.steps)

theorem product_cursor_output {A : Type*} (hp : 0<p) (read : A→Meter (UVBlock fw ell))
    (as : List A) (u : UVBlock fw ell) (fee : ℕ) :
    uvRead hp fw ell (productCursor hp read as u fee).result=
      uvRead hp fw ell u*(as.map (fun a=>uvRead hp fw ell (read a).result)).prod := by
  induction as generalizing u fee with
  | nil => simp only [productCursor,List.map_nil,List.prod_nil,mul_one]
  | cons a as ih =>
    rw [productCursor,ih,mulM_read,List.map_cons,List.prod_cons,mul_assoc]

theorem product_cursor_fee {A : Type*} (hp : 0<p) (read : A→Meter (UVBlock fw ell))
    (as : List A) (u : UVBlock fw ell) (fee : ℕ) :
    fee+bill read as ≤ (productCursor hp read as u fee).steps ∧
      (productCursor hp read as u fee).steps≤
        fee+bill read as+as.length*(mulCap fw.length ell p+2) := by
  induction as generalizing u fee with
  | nil => simp [productCursor,bill]
  | cons a as ih =>
    let x := read a
    let y := mulM hp ⟨u,0⟩ x
    obtain ⟨hL,hU⟩ := ih y.result (fee+y.steps)
    have mh := mulM_cost hp (⟨u,0⟩ : Meter (UVBlock fw ell)) x
    have ml : x.steps≤y.steps := by unfold y mulM; simp only; omega
    simp only [productCursor,bill,List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    change (fee+(x.steps+bill read as)≤(productCursor hp read as y.result (fee+y.steps)).steps) ∧
      (productCursor hp read as y.result (fee+y.steps)).steps≤
        fee+(x.steps+bill read as)+(as.length*(mulCap fw.length ell p+2)+(mulCap fw.length ell p+2))
    change y.steps≤0+x.steps+(mulCap fw.length ell p+2) at mh
    constructor <;> omega

def product64 (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (read : Fin 64→Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  let init := oneM hp he hv
  productCursor hp read (groupOrder 64) init.result init.steps

theorem product64_value (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (read : Fin 64→Meter (UVBlock fw ell)) :
    uvRead hp fw ell (product64 hp he hv read).result=
      ∏ g : Fin 64,uvRead hp fw ell (read g).result := by
  rw [product64,product_cursor_output,groupOrder,List.map_ofFn,List.prod_ofFn]
  simp

theorem product64_bill (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (read : Fin 64→Meter (UVBlock fw ell)) :
    let b := uvWidth fw.length ell p+bill read (groupOrder 64)
    b≤(product64 hp he hv read).steps ∧
      (product64 hp he hv read).steps≤b+64*(mulCap fw.length ell p+2) := by
  simpa only [product64,oneM,groupOrder,List.length_ofFn] using
    product_cursor_fee hp read (groupOrder 64) (oneM hp he hv).result (oneM hp he hv).steps

def modeAddition (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (child : List (J6R15ModeCost.Word q)→Fin 64→Meter (UVBlock fw ell))
    (carry : UVBlock fw ell) (β : List (J6R15ModeCost.Word q)) : Meter (UVBlock fw ell) :=
  addM hp ⟨carry,0⟩ (product64 hp he hv (child β))

theorem mode_fold_value (hp : 0<p) (he : 0<fw.length) (hv : 0<ell)
    (child : List (J6R15ModeCost.Word q)→Fin 64→Meter (UVBlock fw ell))
    (xs : List (List ℕ)) (a : UVBlock fw ell) :
    uvRead hp fw ell (foldExpected (modeAddition hp he hv child) xs a).result=
      uvRead hp fw ell a+
        (xs.map (fun v=>∏ g : Fin 64,uvRead hp fw ell (child (v.map J6R15ModeCost.word) g).result)).sum := by
  induction xs generalizing a with
  | nil => simp only [foldExpected,List.map_nil,List.sum_nil,add_zero]
  | cons v vs ih =>
    simp only [foldExpected]
    rw [ih,modeAddition,addM_read,product64_value,List.map_cons,List.sum_cons,add_assoc]

/-- The two persistent arithmetic accumulators store two literal
UV words. Current emitted vector/cursor, current child result,
temporary arithmetic operands, and verifier data are separate. -/
theorem two_accumulator_payload_width (x y : UVBlock fw ell) :
    (leafPayload x++leafPayload y).length=2*(ell*(fw.length*p)) := by
  rw [List.length_append,leaf_payload_width,leaf_payload_width,two_mul]

#print axioms product_cursor_output
#print axioms product_cursor_fee
#print axioms product64_value
#print axioms product64_bill
#print axioms mode_fold_value
#print axioms two_accumulator_payload_width
end J6R48DFS
