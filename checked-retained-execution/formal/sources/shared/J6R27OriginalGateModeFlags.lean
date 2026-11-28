
import J6R27OriginalGateAxis

/-! Determine the actual generated child's two mode incidences using
the full page identifier (ordered cell *and* copy), its true tiling
bit and its page-specific resident mask bit. Testing only the unordered
cell would not distinguish all printed packet vertices. -/
namespace J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R14LayoutCost
open J6R17ModeTape J6R21Ancestor P11FullPacking J6R9PacketScopes

structure PageRef (q : ℕ) where
  labels : CellWord
  copy : Word q

def modePage {q : ℕ} (x : RawMode q) : PageRef q := ⟨x.key,x.page⟩

noncomputable def pageRef {a b : ℕ} (q : ℕ) (p : Page a b (Fin 64)) : PageRef q :=
  let order := orderedPage a b p
  ⟨wordCell order.1,word order.2.val⟩

theorem page_ref_injective {a b q : ℕ} (fit : b≤2^q) :
    Function.Injective (pageRef (a:=a) (b:=b) q) := by
  intro u v h
  apply (orderedPage a b).injective
  apply Prod.ext
  · exact wordCell_injective a (congrArg PageRef.labels h)
  · apply Fin.ext
    have e := congrArg (fun x : PageRef q=>x.copy.val) h
    change (word ((orderedPage a b u).2.val) : Word q).val=
      (word ((orderedPage a b v).2.val) : Word q).val at e
    rw [word_val ((orderedPage a b u).2.isLt.trans_le fit),
      word_val ((orderedPage a b v).2.isLt.trans_le fit)] at e
    exact e

def cmpPage {q : ℕ} (a b : PageRef q) : Meter Bool :=
  let u := eqRawBits a.labels.1 b.labels.1
  let v := eqRawBits a.labels.2 b.labels.2
  let w := cmpAddr a.copy b.copy
  ⟨u.result && v.result && w.result,u.steps+v.steps+w.steps+6⟩

theorem cmp_page_exact {q : ℕ} (a b : PageRef q) :
    ((cmpPage a b).result=true ↔ a=b) ∧
    (cmpPage a b).steps≤5*a.labels.1.length+5*a.labels.2.length+10*q+15 := by
  have a0 := eq_raw_bits_exact a.labels.1 b.labels.1
  have a1 := eq_raw_bits_exact a.labels.2 b.labels.2
  have w := cmpAddr_exact a.copy b.copy
  constructor
  · simp only [cmpPage,Bool.and_eq_true,a0.1,a1.1,w.1]
    constructor
    · rintro ⟨⟨l,r⟩,c⟩
      have e : a.labels=b.labels := Prod.ext l r
      cases a
      cases b
      simp_all
    · rintro rfl
      exact ⟨⟨rfl,rfl⟩,rfl⟩
  · simp only [cmpPage,w.2]
    have l := a0.2
    have r := a1.2
    omega

def modeFlags {q : ℕ} (axis : List Bool) (m : RawMode q) (wanted : PageRef q)
    (g : Word 6) (maskBit : Bool) : Meter (Bool×Bool) :=
  let own := runtimeGroupPair axis m.key m.tile maskBit
  let pageTest := cmpPage (modePage m) wanted
  let rowTest := eqRawBits g.bits own.result.1
  let colTest := eqRawBits g.bits own.result.2
  ⟨(pageTest.result && rowTest.result,pageTest.result && colTest.result),
    own.steps+pageTest.steps+rowTest.steps+colTest.steps+9⟩

private theorem symbol_inj {a b : Fin 64} (h : symbol a=symbol b) : a=b := by
  have e := congrArg bitsValue h
  rw [symbol_value,symbol_value] at e
  exact Fin.ext e

set_option maxHeartbeats 3500000 in
theorem actual_mode_flags {a b p q : ℕ} (i : Fin a) (width : i.val<q)
    (ticks : List Bool) (clock : ticks.length=i.val) (fit : b≤2^q)
    (mask : MaskFamily a b (Fin 64))
    (x : PacketMode i b (2^(i.val+1)) p)
    (page : Page a b (Fin 64)) (g : Fin 64) :
    let orig := x.1.val
    let tile := tileIndex i x.2.1
    let z := modeFlags ticks (encodeMode (q:=q) i x) (pageRef q page) (word g.val)
      (selectedMaskBit mask orig i)
    (z.result.1=true ↔ orig=page ∧ rowGroup mask i (orig,tile)=g) ∧
      (z.result.2=true ↔ orig=page ∧ colGroup mask i (orig,tile)=g) ∧
      z.steps≤36*i.val+60*a+10*q+326 := by
  let orig := x.1.val
  let t := tileIndex i x.2.1
  let m := encodeMode (q:=q) i x
  let own := runtimeGroupPair ticks m.key m.tile (selectedMaskBit mask orig i)
  let P := cmpPage (modePage m) (pageRef q page)
  have ok := group_pair_is_physical i ticks clock width mask orig x.2.1
  have value : own.result=(symbol (rowGroup mask i (orig,t)),symbol (colGroup mask i (orig,t))) := ok.1
  have fee : own.steps≤36*i.val+238 := ok.2
  have oP : modePage m=pageRef q orig := rfl
  have hp := cmp_page_exact (modePage m) (pageRef q page)
  have pGood : P.result=true↔orig=page := by
    change (cmpPage (modePage m) (pageRef q page)).result=true↔_
    rw [hp.1,oP,(page_ref_injective fit).eq_iff]
  have hW1 : (modePage m).labels.1.length=6*a := by
    simp only [oP,pageRef,wordCell,coordinateLabel_len]
  have hW2 : (modePage m).labels.2.length=6*a := by
    simp only [oP,pageRef,wordCell,coordinateLabel_len]
  have pFee : P.steps≤60*a+10*q+15 := by
    have H := hp.2
    rw [hW1,hW2] at H
    change P.steps≤_ at H
    omega
  let r := eqRawBits (word (q:=6) g.val).bits own.result.1
  let c := eqRawBits (word (q:=6) g.val).bits own.result.2
  have rE := eq_raw_bits_exact (word (q:=6) g.val).bits own.result.1
  have cE := eq_raw_bits_exact (word (q:=6) g.val).bits own.result.2
  have rg : r.result=true ↔ rowGroup mask i (orig,t)=g := by
    apply (show r.result=true ↔ symbol g=own.result.1 from rE.1).trans
    rw [value]
    exact ⟨fun h=>(symbol_inj h).symm,fun h=>congrArg symbol h.symm⟩
  have cg : c.result=true ↔ colGroup mask i (orig,t)=g := by
    apply (show c.result=true ↔ symbol g=own.result.2 from cE.1).trans
    rw [value]
    exact ⟨fun h=>(symbol_inj h).symm,fun h=>congrArg symbol h.symm⟩
  change ((P.result && r.result)=true↔_) ∧ ((P.result && c.result)=true↔_) ∧
    own.steps+P.steps+r.steps+c.steps+9≤_
  refine ⟨?_,?_,?_⟩
  · rw [Bool.and_eq_true,pGood,rg]
  · rw [Bool.and_eq_true,pGood,cg]
  · have RR := rE.2
    have CC := cE.2
    change r.steps≤5*(symbol g).length+2 at RR
    change c.steps≤5*(symbol g).length+2 at CC
    rw [symbol_length] at RR CC
    omega

#print axioms page_ref_injective
#print axioms cmp_page_exact
#print axioms actual_mode_flags
end J6R27OriginalGate



