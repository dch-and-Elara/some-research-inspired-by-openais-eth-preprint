import J6R36ChildFramedRouteCarry
import J6R32RootGeneratedRegistryInputsHalfTape
import J6R34RootAtlasWiden
import J6R19RetainedFrames

/-! Initialize two structured origins from the genuine fixed-width parent
half-port row. Only this documented input record is cut; the opaque
variable-length child header remains unparsed. The optional sidecar is
billed with the existing descriptor, copy and widening primitives. -/
namespace J6R37StructuredRoot
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R34RootAtlas J6R36ChildFramedRoute J6R34ChildPath J6R19Retained
open J6R27OriginalGate J6Mesh
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000

structure RootLanes (m key prec pad : ℕ) where
  gate : Lane (rootHalfWidth m) key prec (pageKeyWidth m+pad)
  packet : Lane (rootHalfWidth m) key prec (pageKeyWidth m+pad)

private def asWord {n : ℕ} (w : A1R10.Word n) : Word n := ⟨w.val,w.property⟩

def birthLanes (m pad : ℕ) {key prec : ℕ} (gate born : Stamp key prec)
    (raw : PortRow (rootHalfWidth m)) : Meter (RootLanes m key prec pad) :=
  let page := cutWord (pageKeyWidth m) raw.body
  let slot := cutWord (a m) page.result.2
  let pg := widened pad (asWord page.result.1)
  let pos := asWord slot.result.1
  let hG := retainHeader raw.body
  let hP := freshHeader (raw.address.bits.headD false) pos
  let g := copyOrigin (⟨gate,none⟩ : Origin key prec (pageKeyWidth m+pad))
  let p := copyOrigin (⟨born,some pg.result⟩ : Origin key prec (pageKeyWidth m+pad))
  let u := duplicateWord raw.address
  let v := duplicateWord raw.address
  ⟨⟨⟨⟨u.result,false⟩,g.result,hG.result⟩,⟨⟨v.result,true⟩,p.result,hP.result⟩⟩,
    page.steps+slot.steps+pg.steps+hG.steps+hP.steps+g.steps+p.steps+u.steps+v.steps+16⟩

def rootLaneSpec (m pad : ℕ) {key prec : ℕ} (original born : Stamp key prec)
    (b : Bool) (F : SeatField (a m) (pageKeyWidth m)) : RootLanes m key prec pad :=
  let row := halfPortSpec m b F
  ⟨⟨⟨row.address,false⟩,⟨original,none⟩,false::row.body⟩,
    ⟨⟨row.address,true⟩,⟨born,some (widened pad F.page).result⟩,true::b::F.slot.bits⟩⟩

def laneFee (m pad key prec : ℕ) :=
  cutWordFee (pageKeyWidth m)+cutWordFee (a m)+wideningFee (pageKeyWidth m) pad+
    (3*(pageKeyWidth m+a m)+5)+(3*a m+5)+originFee key prec (pageKeyWidth m+pad) false+
    originFee key prec (pageKeyWidth m+pad) true+2*(3*rootHalfWidth m+4)+16

theorem birth_lanes_exact (m pad : ℕ) {key prec : ℕ} (original born : Stamp key prec)
    (b : Bool) (F : SeatField (a m) (pageKeyWidth m)) :
    birthLanes m pad original born (halfPortSpec m b F)=⟨rootLaneSpec m pad original born b F,laneFee m pad key prec⟩ := by
  let P : A1R10.Word (pageKeyWidth m) := ⟨F.page.bits,F.page.size⟩
  let U : A1R10.Word (a m) := ⟨F.slot.bits,F.slot.size⟩
  have Pp := cutWord_exact P F.slot.bits
  have Pu := cutWord_exact U []
  change (cutWord (pageKeyWidth m) (F.page.bits++F.slot.bits)).result=(P,F.slot.bits) ∧ _ at Pp
  change (cutWord (a m) (F.slot.bits++[])).result=(U,[]) ∧ _ at Pu
  simp only [List.append_nil] at Pu
  unfold birthLanes rootLaneSpec
  dsimp only
  change (⟨_,_⟩ : Meter (RootLanes m key prec pad))=_
  simp only [show (halfPortSpec m b F).body=F.page.bits++F.slot.bits from rfl,
    Pp.1,Pu.1,widened_exact,retain_header_exact,fresh_header_exact,
    duplicate_word_exact,copy_origin_exact,Option.isSome_none,Option.isSome_some,
    List.length_append,F.page.size,F.slot.size]
  congr 1
  rw [show (cutWord (pageKeyWidth m) (F.page.bits++F.slot.bits)).steps=_ from Pp.2,
    show (cutWord (a m) F.slot.bits).steps=_ from Pu.2]
  unfold laneFee
  omega

theorem two_actual_root_endpoints (m pad : ℕ) {key prec : ℕ} (original born : Stamp key prec)
    (b : Bool) (F : SeatField (a m) (pageKeyWidth m)) :
    let R := (birthLanes m pad original born (halfPortSpec m b F)).result
    R.gate.id≠R.packet.id ∧ R.gate.origin.pageKey=none ∧
      R.packet.origin.pageKey=some (widened pad F.page).result := by
  rw [birth_lanes_exact]
  refine ⟨fun e=>?_,rfl,rfl⟩
  exact Bool.false_ne_true (congrArg RouteID.col e)

#print axioms birth_lanes_exact
#print axioms two_actual_root_endpoints
end J6R37StructuredRoot