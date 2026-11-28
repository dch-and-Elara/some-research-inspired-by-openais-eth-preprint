import J6R34ChildPathWireSource
import J6R26DescriptorTreeTags

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11500000

/-! A separately priced structured sidecar for a native child. The
printed R26 bit header is left unchanged. No variable-length body is
read by parsing its unframed byte concatenation. -/
namespace J6R36ChildFramedRoute
open scoped Polynomial Classical
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R27OriginalGate J6R34ChildPath

structure RouteID (edgeWidth : ℕ) where
  edge : Word edgeWidth
  col : Bool

structure Origin (key prec page : ℕ) where
  stamp : Stamp key prec
  pageKey : Option (Word page)

structure Addon (owner a key prec page : ℕ) where
  oldOwner : Word owner
  oldOrigin : Origin key prec page
  parentWasCol : Bool
  parentSlot : Word a
  newPage : Word page

structure Lane (w key prec page : ℕ) where
  id : RouteID w
  origin : Origin key prec page
  body : List Bool

structure FramedEdge (w owner key prec page : ℕ) where
  oldOwner : Word owner
  left : Lane w key prec page
  right : Lane w key prec page

/-- Copy a previous live reference, including its particular inner page
when it is not an original unpaged entry. -/
def copyOrigin {key prec page : ℕ} (s : Origin key prec page) : Meter (Origin key prec page) :=
  let st := duplicateStamp s.stamp
  match s.pageKey with
  | none => ⟨⟨st.result,none⟩,st.steps+4⟩
  | some pageKey =>
    let pg := duplicateWord pageKey
    ⟨⟨st.result,some pg.result⟩,st.steps+pg.steps+6⟩

def originFee (key prec page : ℕ) (present : Bool) :=
  3*key+3*prec+12+(if present then 3*page+10 else 4)

theorem copy_origin_exact {key prec page : ℕ} (s : Origin key prec page) :
    copyOrigin s=⟨s,originFee key prec page s.pageKey.isSome⟩ := by
  obtain ⟨tag,pg⟩ := s
  cases pg <;> simp only [copyOrigin,duplicate_stamp_exact,duplicate_word_exact,
    Option.isSome_none,Option.isSome_some,originFee,Bool.false_eq_true,if_false,if_true]
  congr 1

def frameView {w owner a key prec page : ℕ} (id : Word key) (recv : Word prec)
    (raw : PortRow w) (aux : Addon owner a key prec page) : FramedEdge w owner key prec page :=
  ⟨aux.oldOwner,
    ⟨⟨raw.address,false⟩,aux.oldOrigin,false::raw.body⟩,
    ⟨⟨raw.address,true⟩,⟨⟨id,recv⟩,some aux.newPage⟩,
      true::aux.parentWasCol::aux.parentSlot.bits⟩⟩

def writeFrame {w owner a key prec page : ℕ} (id : Word key) (recv : Word prec)
    (raw : PortRow w) (aux : Addon owner a key prec page) : Meter (FramedEdge w owner key prec page) :=
  let u := duplicateWord raw.address
  let v := duplicateWord raw.address
  let own := duplicateWord aux.oldOwner
  let before := copyOrigin aux.oldOrigin
  let after := copyOrigin (⟨⟨id,recv⟩,some aux.newPage⟩ : Origin key prec page)
  let hL := retainHeader raw.body
  let hR := freshHeader aux.parentWasCol aux.parentSlot
  ⟨⟨own.result,⟨⟨u.result,false⟩,before.result,hL.result⟩,
      ⟨⟨v.result,true⟩,after.result,hR.result⟩⟩,
    u.steps+v.steps+own.steps+before.steps+after.steps+hL.steps+hR.steps+14⟩

def frameFee (w owner a key prec page bodyLen : ℕ) (present : Bool) :=
  2*(3*w+4)+(3*owner+4)+originFee key prec page present+originFee key prec page true+
    (3*bodyLen+5)+(3*a+5)+14

theorem write_frame_exact {w owner a key prec page : ℕ} (id : Word key) (recv : Word prec)
    (raw : PortRow w) (aux : Addon owner a key prec page) :
    writeFrame id recv raw aux=
      ⟨frameView id recv raw aux,frameFee w owner a key prec page raw.body.length aux.oldOrigin.pageKey.isSome⟩ := by
  simp only [writeFrame,duplicate_word_exact,copy_origin_exact,retain_header_exact,
    fresh_header_exact,Option.isSome_some,frameView,frameFee]
  congr 1
  dsimp only
  omega

def attachRoute {w owner a key prec page : ℕ}
    (bank : List (RefRow w (Addon owner a key prec page))) (id : Word key) (recv : Word prec)
    (r : PortRow w) : Meter (Option (FramedEdge w owner key prec page)) :=
  let sel := locate r.address bank
  match sel.result with
  | none => ⟨none,sel.steps+3⟩
  | some aux =>
    let out := writeFrame id recv r aux
    ⟨some out.result,sel.steps+out.steps+5⟩

def frameBatch {w owner a key prec page : ℕ}
    (bank : List (RefRow w (Addon owner a key prec page))) (id : Word key) (recv : Word prec) :
    List (PortRow w)→Meter (Option (List (FramedEdge w owner key prec page)))
  | []=>⟨some [],3⟩
  | r::rs=>
    let h := attachRoute bank id recv r
    match h.result with
    | none => ⟨none,h.steps+4⟩
    | some x =>
      let rest := frameBatch bank id recv rs
      ⟨rest.result.map (x::·),h.steps+rest.steps+4⟩

def selectedFrame {w owner a key prec page : ℕ} (group : Word 6) (raw : List (PortRow w))
    (bank : List (RefRow w (Addon owner a key prec page))) (id : Word key) (recv : Word prec) :
    Meter (Option (List (FramedEdge w owner key prec page))) :=
  let sel := selectPorts group raw
  let frames := frameBatch bank id recv sel.result
  ⟨frames.result,sel.steps+frames.steps+5⟩

/-- The two endpoints of a genuine selected child edge are never
coalesced by a shared old owner, page, or physical seat coordinate. -/
theorem paired_half_ids {w owner a key prec page : ℕ} (o : Word key) (precWord : Word prec)
    (r : PortRow w) (d : Addon owner a key prec page) :
    let F := (writeFrame o precWord r d).result
    F.left.id=⟨r.address,false⟩ ∧ F.right.id=⟨r.address,true⟩ ∧
      F.left.id≠F.right.id ∧ F.left.origin=d.oldOrigin ∧
      F.right.origin=⟨⟨o,precWord⟩,some d.newPage⟩ := by
  rw [write_frame_exact]
  refine ⟨rfl,rfl,fun h=>?_,rfl,rfl⟩
  exact Bool.false_ne_true (congrArg RouteID.col h)

#print axioms copy_origin_exact
#print axioms write_frame_exact
#print axioms paired_half_ids
end J6R36ChildFramedRoute
