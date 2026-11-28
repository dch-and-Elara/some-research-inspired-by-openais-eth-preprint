import J6R18ChildWriteSource
import J6R18ChildWriteBytes

/-! A literal new packet-entry evaluator, from one requested port
assignment and the serialized per-packet mode data. Only this same
entry is written; neither the Boolean entry cube nor the child
contraction is materialized by this routine. -/
namespace J6R18ChildWrite
open scoped BigOperators Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates AOracleWitness
open A1R10 A1R11 A1R12 P1DyadicGrid
open MvPolynomial

def packRows {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (i : Fin a) (b : ℕ)
    (rows cols : List (SlotBit a)) (modes : List (ModeInput a p i q)) :
    Meter (List (List (Term fw ell))) :=
  A1R12.mapMeter (affineRowWords hp he hv z t i b cols modes)
    ((modes.length+1)*(b+uvWidth fw.length ell p+4)) rows

def rowWriteCap (a e ell p i q b c m r : ℕ) (hp : 0<p) :=
  r*(affineRowFee a e ell p i q b c m hp+(m+1)*(b+uvWidth e ell p+4)+4)

theorem packRows_exact {p ell a q m : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a)
    (i : Fin a) (b : ℕ) (rows cols : List (SlotBit a)) (modes : Fin m→ModeInput a p i q)
    (hc : ∀ j,(modes j).code=encodeBits b j.succ.val) :
    let u := packRows hp he hv z t i b rows cols (List.ofFn modes)
    let fs := rows.map (typedRowWords hp he hv z t i cols modes)
    u.result=fs.map (List.map (termEncode b)) ∧
      u.steps≤rowWriteCap a fw.length ell p i.val q b cols.length m rows.length hp := by
  let G := affineRowWords hp he hv z t i b cols (List.ofFn modes)
  have hh := A1R12.mapMeter_exact G ((m+1)*(b+uvWidth fw.length ell p+4))
    (affineRowFee a fw.length ell p i.val q b cols.length m hp) rows
    (fun r _=>(affineRowWords_exact hp he hv z t ht i b cols modes hc r).2)
  obtain ⟨hr,hFee⟩ := hh
  constructor
  · unfold packRows
    rw [List.length_ofFn,hr,List.map_map]
    exact List.map_congr_left (fun r _=>(affineRowWords_exact hp he hv z t ht i b cols modes hc r).1)
  · simpa only [packRows,List.length_ofFn,rowWriteCap] using hFee

def packetResult {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (i : Fin a) (b : ℕ)
    (rows cols : List (SlotBit a)) (modes : List (ModeInput a p i q)) : Meter (UVBlock fw ell) :=
  let f := packRows hp he hv z t i b rows cols modes
  let tests := prepareChecks b modes
  let one := oneM hp he hv
  let A := evalRows hp b q tests.result f.result [] one.result
  let Y := sourceProduct hp he hv i cols modes
  let Z := uvMul hp A.result Y.result
  ⟨Z.result,f.steps+tests.steps+one.steps+A.steps+Y.steps+Z.steps+12⟩

def packetFee (a e ell p i q b r c m : ℕ) (hp : 0<p) :=
  let W := uvWidth e ell p
  rowWriteCap a e ell p i q b c m r hp+
    m*((2*b+4*q+8)+(b+q)+4)+W+
    treeFee W (m+1) (leafFee e ell p m r b q) (choiceFee e ell p b hp) r+
    W+m*(sourcePowerFee a e ell p q c hp+mulCap e ell p+2)+mulCap e ell p+12

theorem packetResult_exact {p ell a q m : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a)
    (i : Fin a) (b : ℕ) (hq : 0<q) (hb : m+1≤2^b)
    (rows cols : List (SlotBit a)) (hr : rows.length<2^q) (modes : Fin m→ModeInput a p i q)
    (hc : ∀ j,(modes j).code=encodeBits b j.succ.val) :
    let V := packetResult hp he hv z t i b rows cols (List.ofFn modes)
    let fs := rows.map (fun r=>(typedRowWords hp he hv z t i cols modes r).map (termMeaning hp))
    uvRead hp fw ell V.result=
      coeff (requestedProfile modes) (rowsPoly fs)*((List.ofFn modes).map (sourcedValue cols)).prod ∧
      V.steps≤packetFee a fw.length ell p i.val q b rows.length cols.length m hp := by
  let T := List.ofFn modes
  let F := packRows hp he hv z t i b rows cols T
  let B := prepareChecks b T
  let one := oneM hp he hv
  let X := evalRows hp b q B.result F.result [] one.result
  let Y := sourceProduct hp he hv i cols T
  let Z := uvMul hp X.result Y.result
  let rs := rows.map (typedRowWords hp he hv z t i cols modes)
  obtain ⟨hF,fC⟩ := packRows_exact hp he hv z t ht i b rows cols modes hc
  obtain ⟨hB,bC⟩ := prepareChecks_exact b modes hc
  have hL : rs.length=rows.length := List.length_map _
  have hSubset : ∀ row∈rs,row.length≤m+1 := by
    intro row hx
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
    simp [typedRowWords]
  have H := evalRows_exact hp b q hq hb (requestedProfile modes) (profile_fits modes)
    rows.length (m+1) hr rs hSubset [] (by simp [hL]) one.result
  change F.result=_ at hF
  change B.result=_ at hB
  rw [← hF,← hB,hL] at H
  obtain ⟨hX,xC⟩ := H
  obtain ⟨hY,yC⟩ := sourceProduct_exact hp he hv i cols T
  have hN : T.length=m := List.length_ofFn
  rw [hN] at yC
  have hOne : uvRead hp fw ell one.result=1 := oneM_read hp he hv
  change uvRead hp fw ell X.result=_ at hX
  change X.steps≤_ at xC
  obtain ⟨hZ,zC⟩ := uvMul_native_bit_cost hp X.result Y.result
  constructor
  · change uvRead hp fw ell Z.result=_
    rw [show uvRead hp fw ell Z.result=_ from hZ,hX,hY,hOne,List.map_nil,coefficients_exact]
    simp only [rs,List.map_map,Function.comp_def,T]
  · change F.steps+B.steps+one.steps+X.steps+Y.steps+Z.steps+12≤_
    change F.steps≤_ at fC
    change B.steps≤_ at bC
    change Y.steps≤_ at yC
    change Z.steps≤mulCap fw.length ell p at zC
    have oneFee : one.steps=uvWidth fw.length ell p := rfl
    rw [oneFee]
    dsimp only [packetFee]
    omega

def packedEntry {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (tag : J6R15ModeCost.Word q)
    (z : UVBlock fw ell) (t : ℤ) (i : Fin a) (b : ℕ)
    (rows cols : List (SlotBit a)) (modes : List (ModeInput a p i q)) : Meter (List Bool) :=
  let x := packetResult hp he hv z t i b rows cols modes
  let u := writeEntry tag x.result
  ⟨u.result,x.steps+u.steps+4⟩

theorem packedEntry_cost {p ell a q m : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (tag : J6R15ModeCost.Word q)
    (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a) (i : Fin a) (b : ℕ) (hq : 0<q) (hb : m+1≤2^b)
    (rows cols : List (SlotBit a)) (hr : rows.length<2^q) (modes : Fin m→ModeInput a p i q)
    (hc : ∀ j,(modes j).code=encodeBits b j.succ.val) :
    let v := packedEntry hp he hv tag z t i b rows cols (List.ofFn modes)
    let fs := rows.map (fun r=>(typedRowWords hp he hv z t i cols modes r).map (termMeaning hp))
    ∃ w : UVBlock fw ell,
      frameRead q p fw.length ell v.result=(tag.bits,w.val.map (fun u=>u.val.map Subtype.val)) ∧
      uvRead hp fw ell w=coeff (requestedProfile modes) (rowsPoly fs)*
        ((List.ofFn modes).map (sourcedValue cols)).prod ∧
      v.steps≤packetFee a fw.length ell p i.val q b rows.length cols.length m hp+
        (4*q+6*ell*(fw.length*p+1)+16)+4 := by
  let w := packetResult hp he hv z t i b rows cols (List.ofFn modes)
  obtain ⟨hE,hC⟩ := packetResult_exact hp he hv z t ht i b hq hb rows cols hr modes hc
  obtain ⟨_,hWrite,wC⟩ := write_roundtrip tag w.result
  refine ⟨w.result,hWrite,hE,?_⟩
  change w.steps+(writeEntry tag w.result).steps+4≤_
  rw [wC]
  exact Nat.add_le_add_right (Nat.add_le_add_right hC _) _

#print axioms packRows_exact
#print axioms packetResult_exact
#print axioms packedEntry_cost
end J6R18ChildWrite


