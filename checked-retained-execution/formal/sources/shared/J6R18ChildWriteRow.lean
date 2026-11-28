import J6R18ChildWriteOperands
import J6R18ChildWriteExpand

/-! Construct one charged affine coefficient row from local physical
slot/bit records and the ordered descriptor list. The bits indicating
membership in this packet/group are validated by the physical adapter. -/
namespace J6R18ChildWrite
open scoped BigOperators Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape AOracleCoordinates AOracleWitness
open A1R10 A1R11 A1R12
open P1DyadicGrid J6R9PacketTiles J6R9PacketLocal
open AOracleSuccinctPhysical

structure ModeInput (a p : ℕ) (i : Fin a) (q : ℕ) where
  code : List Bool
  tile : J6R15ModeCost.Word (i.val+1)
  order : Fin (p-1)
  targeted : Bool
  sourced : Bool
  beta : J6R15ModeCost.Word q

def localSum {p ell a : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ)
    (x : SlotBit a) (cols : List (SlotBit a)) : Meter (UVBlock fw ell) :=
  sumUV hp (onColumn hp he hv z t x) cols

noncomputable def localMeaning {R : Type*} [CommRing R] (p : ℕ) (hnil : (2:R)^p=0)
    {a : ℕ} (t : ℤ) (z : R) (x : SlotBit a) (cols : List (SlotBit a)) : R :=
  (cols.map (fun y=>(W a t ((y.index.val:ℤ)-(x.index.val:ℤ))).eval₂
    (J6ZeroTransport.reduceAt p hnil) z * bit R y.assigned)).sum

theorem localSum_exact {p ell a : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a)
    (x : SlotBit a) (cols : List (SlotBit a)) :
    let hnil := double_quotient_two_nilpotent (Modulus p hp fw) ell
    let v := localSum hp he hv z t x cols
    uvRead hp fw ell v.result=localMeaning p hnil t (uvRead hp fw ell z) x cols ∧
      v.steps≤uvWidth fw.length ell p+cols.length*(columnFee a fw.length ell p hp+addCap fw.length ell p hp+2) :=
  sumUV_exact hp _ _ _ cols (fun y _=>onColumn_exact hp he hv z t ht x y)

def unsignedCross {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell)
    (t : ℤ) (i : Fin a) (r : SlotBit a) (m : ModeInput a p i q) : Meter (UVBlock fw ell) :=
  if m.targeted then
    padCost (crossingGen hp he hv z a i.val m.order.val t r.index.val m.tile.val) (16*(a+q+3)^2)
  else plainZero hp

def unsignedCap (a e ell p i q : ℕ) (hp : 0<p) : ℕ :=
  crossingGenCap e ell p a i p hp+uvWidth e ell p+16*(a+q+3)^2

def crossMeaning {R : Type*} [CommRing R] {a p q : ℕ} {i : Fin a}
    (t : ℤ) (z : R) (r : SlotBit a) (m : ModeInput a p i q) : R :=
  if m.targeted then crossCell p a i.val m.order.val t r.index.val m.tile.val z else 0

theorem unsignedCross_exact {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a)
    (i : Fin a) (r : SlotBit a) (m : ModeInput a p i q) :
    let u := unsignedCross hp he hv z t i r m
    uvRead hp fw ell u.result=crossMeaning t (uvRead hp fw ell z) r m ∧
      u.steps≤unsignedCap a fw.length ell p i.val q hp := by
  by_cases H : m.targeted=true
  · obtain ⟨h,c⟩ := crossingGen_exact hp he hv z a i.val m.order.val t _ _ ht r.index.isLt
      (J6R15ModeCost.val_lt m.tile)
    have hM : m.order.val≤p := by have := m.order.isLt; omega
    have C := c.trans (crossingCap_mono _ _ _ _ _ _ _ hp hM)
    simp only [unsignedCross,crossMeaning,H,if_true,padCost]
    refine ⟨h,?_⟩
    unfold unsignedCap
    omega
  · rw [unsignedCross,crossMeaning,if_neg H,if_neg H]
    constructor
    · exact uvZero_read hp fw ell
    · unfold plainZero unsignedCap
      dsimp only
      omega

def variableTerm {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell)
    (t : ℤ) (i : Fin a) (r : SlotBit a) (m : ModeInput a p i q) : Meter (Term fw ell) :=
  let s := signedFactor hp he r.assigned (unsignedCross hp he hv z t i r m)
  ⟨⟨m.code,s.result⟩,s.steps+2*m.code.length+6⟩

def variableFee (a e ell p i q b : ℕ) (hp : 0<p) : ℕ :=
  unsignedCap a e ell p i q hp+affineExtra e ell p hp+2*b+6

theorem variableTerm_exact {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a)
    (i : Fin a) (r : SlotBit a) (m : ModeInput a p i q) (b : ℕ) (hb : m.code.length=b) :
    let s := variableTerm hp he hv z t i r m
    s.result.code=m.code ∧
      uvRead hp fw ell s.result.value=LiteralPortCompiler.slope r.assigned*crossMeaning t (uvRead hp fw ell z) r m ∧
      s.steps≤variableFee a fw.length ell p i.val q b hp := by
  obtain ⟨hm,hC⟩ := unsignedCross_exact hp he hv z t ht i r m
  obtain ⟨h,hD⟩ := signedFactor_exact hp he r.assigned (unsignedCross hp he hv z t i r m)
  refine ⟨rfl,by rw [variableTerm,h,hm],?_⟩
  unfold variableTerm variableFee
  dsimp only
  rw [hb]
  omega

def affineRowWords {p ell a q : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (i : Fin a) (b : ℕ)
    (cols : List (SlotBit a)) (modes : List (ModeInput a p i q)) (r : SlotBit a) :
    Meter (List (Term fw ell)) :=
  let L := baseFactor hp he hv r.assigned (localSum hp he hv z t r cols)
  let X := A1R12.mapMeter (variableTerm hp he hv z t i r) (uvWidth fw.length ell p+b) modes
  ⟨⟨encodeBits b 0,L.result⟩::X.result,L.steps+X.steps+4*b+2*uvWidth fw.length ell p+12⟩

def affineRowFee (a e ell p i q b col m : ℕ) (hp : 0<p) : ℕ :=
  uvWidth e ell p+col*(columnFee a e ell p hp+addCap e ell p hp+2)+affineExtra e ell p hp+
    m*(variableFee a e ell p i q b hp+(uvWidth e ell p+b)+4)+4*b+2*uvWidth e ell p+12

def typedRowWords {p ell a q m : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (i : Fin a)
    (cols : List (SlotBit a)) (modes : Fin m→ModeInput a p i q) (r : SlotBit a) :
    List (Fin (m+1)×UVBlock fw ell) :=
  (0,(baseFactor hp he hv r.assigned (localSum hp he hv z t r cols)).result)::
    (List.finRange m).map (fun j=>(j.succ,(variableTerm hp he hv z t i r (modes j)).result.value))

theorem affineRowWords_exact {p ell a q m : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a) (i : Fin a) (b : ℕ)
    (cols : List (SlotBit a)) (modes : Fin m→ModeInput a p i q)
    (codes : ∀ j,(modes j).code=encodeBits b j.succ.val) (r : SlotBit a) :
    let w := affineRowWords hp he hv z t i b cols (List.ofFn modes) r
    w.result=(typedRowWords hp he hv z t i cols modes r).map (termEncode b) ∧
      w.steps≤affineRowFee a fw.length ell p i.val q b cols.length m hp := by
  let F := variableTerm (q:=q) hp he hv z t i r
  let B := baseFactor hp he hv r.assigned (localSum hp he hv z t r cols)
  let W := uvWidth fw.length ell p
  have Hloc := (localSum_exact hp he hv z t ht r cols).2
  have Hb := (baseFactor_exact hp he hv r.assigned (localSum hp he hv z t r cols)).2
  change B.steps≤_ at Hb
  obtain ⟨hv',ht'⟩ := A1R12.mapMeter_exact F (W+b) (variableFee a fw.length ell p i.val q b hp)
    (List.ofFn modes) (fun x hx=>by
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact (variableTerm_exact hp he hv z t ht i r _ b (by rw [codes,encodeBits_length])).2.2)
  rw [List.length_ofFn] at ht'
  constructor
  · unfold affineRowWords typedRowWords
    dsimp only
    rw [hv',List.ofFn_eq_map,List.map_map,List.map_cons,List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    change Term.mk (modes j).code (F (modes j)).result.value=
      Term.mk (encodeBits b j.succ.val) (F (modes j)).result.value
    rw [codes]
  · unfold affineRowWords affineRowFee
    dsimp only
    change B.steps+(A1R12.mapMeter F (W+b) (List.ofFn modes)).steps+4*b+2*W+12≤_
    unfold W at ht' ⊢
    omega

#print axioms localSum_exact
#print axioms unsignedCross_exact
#print axioms variableTerm_exact
#print axioms affineRowWords_exact
end J6R18ChildWrite


