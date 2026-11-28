import J6R18ChildWriteKernelCross
import A1R12Numeric
import J6R14LayoutCostRound
import J6R15ModeCostCursor

/-! Numeric operands for one real packet row or source tile. Input slots
and bits are explicit; the Cauchy, crossing and moment values are produced
at the claimed receiving precision, not accepted as a value table. -/
namespace J6R18ChildWrite
open scoped Classical BigOperators Polynomial
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates
open A1R9 A1R10 A1R11 A1R12
open P1DyadicGrid J6R9PacketTiles AOracleSuccinctNative AOracleSuccinctPhysical
open J6R9PacketLocal J6R9PacketCoeff P1DyadicGridBridge

structure SlotBit (a : ℕ) where
  slot : J6R15ModeCost.Word a
  assigned : Bool

def SlotBit.index {a : ℕ} (v : SlotBit a) : Fin (2^a) :=
  ⟨v.slot.val,J6R15ModeCost.val_lt v.slot⟩

def subM {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (x y : Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  let z := uvSub hp he x.result y.result
  ⟨z.result,x.steps+y.steps+z.steps+2⟩

theorem subM_exact {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (x y : Meter (UVBlock fw ell)) :
    (uvRead hp fw ell (subM hp he x y).result=uvRead hp fw ell x.result-uvRead hp fw ell y.result) ∧
      (subM hp he x y).steps≤x.steps+y.steps+subCap fw.length ell p hp+2 := by
  obtain ⟨h,hc⟩ := uvSub_exact hp he x.result y.result
  exact ⟨h,Nat.add_le_add_right (Nat.add_le_add_left hc _) _⟩

def plainZero {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)} : Meter (UVBlock fw ell) :=
  ⟨uvZero hp fw ell,uvWidth fw.length ell p⟩

def baseFactor {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)} (he : 0<fw.length) (hv : 0<ell)
    (y : Bool) (x : Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  if y then padCost x 4 else subM hp he (oneM hp he hv) x

def signedFactor {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)} (he : 0<fw.length)
    (y : Bool) (x : Meter (UVBlock fw ell)) : Meter (UVBlock fw ell) :=
  if y then padCost x 4 else subM hp he (plainZero hp) x

def affineExtra (e ell p : ℕ) (hp : 0<p) : ℕ :=
  uvWidth e ell p+subCap e ell p hp+4

theorem baseFactor_exact {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)} (he : 0<fw.length)
    (hv : 0<ell) (y : Bool) (x : Meter (UVBlock fw ell)) :
    let z := baseFactor hp he hv y x
    uvRead hp fw ell z.result=LiteralPortCompiler.affine y (uvRead hp fw ell x.result) ∧
      z.steps≤x.steps+affineExtra fw.length ell p hp := by
  cases y with
  | true =>
    simp only [baseFactor,if_true,LiteralPortCompiler.affine,padCost,true_and,affineExtra]
    omega
  | false =>
    obtain ⟨h,hc⟩ := subM_exact hp he (oneM hp he hv) x
    refine ⟨by simpa only [baseFactor,Bool.false_eq_true,if_false,oneM_read,LiteralPortCompiler.affine] using h,?_⟩
    change (subM hp he (oneM hp he hv) x).steps≤_
    unfold affineExtra
    change (subM hp he (oneM hp he hv) x).steps≤uvWidth fw.length ell p+x.steps+subCap _ _ _ _+2 at hc
    omega

theorem signedFactor_exact {p ell : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)} (he : 0<fw.length)
    (y : Bool) (x : Meter (UVBlock fw ell)) :
    let z := signedFactor hp he y x
    uvRead hp fw ell z.result=LiteralPortCompiler.slope y*(uvRead hp fw ell x.result) ∧
      z.steps≤x.steps+affineExtra fw.length ell p hp := by
  cases y with
  | true =>
    simp only [signedFactor,if_true,LiteralPortCompiler.slope,padCost,one_mul,true_and,affineExtra]
    omega
  | false =>
    obtain ⟨h,hc⟩ := subM_exact hp he (plainZero hp) x
    refine ⟨by simpa only [signedFactor,Bool.false_eq_true,if_false,plainZero,uvZero_read,zero_sub,
      LiteralPortCompiler.slope,neg_mul,one_mul] using h,?_⟩
    change (subM hp he (plainZero hp) x).steps≤_
    unfold affineExtra
    change (subM hp he (plainZero hp) x).steps≤uvWidth fw.length ell p+x.steps+subCap _ _ _ _+2 at hc
    omega

def onColumn {p ell a : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (x y : SlotBit a) :
    Meter (UVBlock fw ell) :=
  if y.assigned then
    padCost (modularGen hp he hv z a t ((y.index.val:ℤ)-(x.index.val:ℤ))) (16*(a+3)^2)
  else padCost (plainZero hp) (4*a+8)

def columnFee (a e ell p : ℕ) (hp : 0<p) : ℕ :=
  modularGenCap e ell p a hp+uvWidth e ell p+20*(a+3)^2+8

theorem onColumn_exact {p ell a : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a)
    (x y : SlotBit a) :
    let R := Truncated (Modulus p hp fw) ell
    let hnil := double_quotient_two_nilpotent (Modulus p hp fw) ell
    let k := (y.index.val:ℤ)-(x.index.val:ℤ)
    let v := onColumn hp he hv z t x y
    uvRead hp fw ell v.result=(W a t k).eval₂ (J6ZeroTransport.reduceAt p hnil)
      (uvRead hp fw ell z)*bit R y.assigned ∧ v.steps≤columnFee a fw.length ell p hp := by
  let k := (y.index.val:ℤ)-(x.index.val:ℤ)
  have hg : k∈grid a := literal_slot_difference x.index y.index
  obtain ⟨h,hFee⟩ := modularGen_exact hp he hv z a t k ht hg
  rw [← W_is_modular p (double_quotient_two_nilpotent (Modulus p hp fw) ell) ht hg] at h
  by_cases ha : y.assigned=true
  · simp only [onColumn,ha,if_true,padCost,bit,mul_one]
    refine ⟨h,?_⟩
    change (modularGen hp he hv z a t k).steps+16*(a+3)^2≤_
    unfold columnFee
    nlinarith
  · have ha' : y.assigned=false := Bool.eq_false_iff.mpr ha
    simp only [onColumn,ha',Bool.false_eq_true,if_false,padCost,plainZero,bit,uvZero_read,mul_zero,true_and]
    unfold columnFee
    nlinarith

def tileEquals {a : ℕ} (i : Fin a) (x : SlotBit a)
    (tileWord : J6R15ModeCost.Word (i.val+1)) : Meter Bool :=
  let s := eqWord (x.slot.bits.take (i.val+1)) tileWord.bits
  ⟨s.result,s.steps+4*a+8⟩

theorem tileEquals_exact {a : ℕ} (i : Fin a) (x : SlotBit a)
    (target : J6R15ModeCost.Word (i.val+1)) :
    ((tileEquals i x target).result=true ↔ tile i.val x.index.val=target.val) ∧
    (tileEquals i x target).steps≤14*a+8 := by
  have hL : (x.slot.bits.take (i.val+1)).length=i.val+1 := by
    rw [List.length_take,x.slot.size,min_eq_left i.isLt]
  obtain ⟨he,hc⟩ := eqWord_exact (x.slot.bits.take (i.val+1)) target.bits (hL.trans target.size.symm)
  have hn := J6R14LayoutCost.take_value (i.val+1) x.slot.bits
  constructor
  · change ((eqWord (x.slot.bits.take (i.val+1)) target.bits).result=true ↔ _)
    rw [he,hn]
    rfl
  · change (eqWord (x.slot.bits.take (i.val+1)) target.bits).steps+4*a+8≤_
    rw [hc,hL]
    have := i.isLt
    omega

def onTile {p ell a : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (i : Fin a) (x : SlotBit a)
    (target : J6R15ModeCost.Word (i.val+1)) (b : ℕ) : Meter (UVBlock fw ell) :=
  let k := tileEquals i x target
  if k.result && x.assigned then
    let y := asLowWord p (x.slot.bits.drop (i.val+1))
    let r := momentCell hp he hv y b
    ⟨r.result,r.steps+k.steps+4*(a+p+2)⟩
  else ⟨uvZero hp fw ell,k.steps+uvWidth fw.length ell p+4⟩

def tileFee (a e ell p b : ℕ) : ℕ :=
  14*a+8+4*(a+p+2)+p+2+b*(32*(p+1)^2+4)+uvWidth e ell p+4

theorem onTile_exact {p ell a : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (i : Fin a) (x : SlotBit a)
    (target : J6R15ModeCost.Word (i.val+1)) (b : ℕ) :
    let R := Truncated (Modulus p hp fw) ell
    let v := onTile hp he hv i x target b
    uvRead hp fw ell v.result=
      (if tile i.val x.index.val=target.val then (coord i.val x.index.val:R)^b*bit R x.assigned else 0) ∧
      v.steps≤tileFee a fw.length ell p b := by
  let k := tileEquals i x target
  let y := asLowWord p (x.slot.bits.drop (i.val+1))
  obtain ⟨hk,hC⟩ := tileEquals_exact i x target
  have hq : wordRead y=(AOracleSuccinctPacket.quotient i.val x.index.val:ZMod (2^p)) := by
    rw [show wordRead y=_ from asLowWord_read _ _,J6R14LayoutCost.drop_value]
    rfl
  obtain ⟨h,hCost⟩ := momentCell_exact hp he hv y i.val x.index.val b hq
  change uvRead hp fw ell (momentCell hp he hv y b).result=(_^b) at h
  change k.steps≤14*a+8 at hC
  change (momentCell hp he hv y b).steps≤p+2+b*(32*(p+1)^2+4)+uvWidth fw.length ell p at hCost
  by_cases heq : tile i.val x.index.val=target.val
  · have hb : k.result=true := hk.mpr heq
    cases hX : x.assigned
    · have ht' : (tileEquals i x target).result=true := hb
      simp only [onTile,ht',hX,Bool.true_and,Bool.false_eq_true,if_false,heq,if_true,bit,mul_zero,uvZero_read,true_and]
      change k.steps+uvWidth fw.length ell p+4≤_
      unfold tileFee
      omega
    · simp only [onTile,show (tileEquals i x target).result=true from hb,
        hX,Bool.and_self,if_true,heq,bit,mul_one]
      refine ⟨h,?_⟩
      change (momentCell hp he hv y b).steps+k.steps+4*(a+p+2)≤_
      unfold tileFee
      omega
  · have hb : k.result=false := Bool.eq_false_iff.mpr (fun e=>heq (hk.mp e))
    simp only [onTile,show (tileEquals i x target).result=false from hb,
      Bool.false_and,Bool.false_eq_true,if_false,heq,uvZero_read,true_and,tileFee]
    change k.steps+_+4≤_
    omega

#print axioms baseFactor_exact
#print axioms signedFactor_exact
#print axioms onColumn_exact
#print axioms tileEquals_exact
#print axioms onTile_exact
end J6R18ChildWrite



