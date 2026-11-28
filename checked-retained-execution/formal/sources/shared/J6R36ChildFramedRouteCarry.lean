import J6R36ChildFramedRouteCore

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! Route identifiers can be retained as typed pairs, or copied into
one more internal bit for another child descriptor. This optional
framed ABI is charged separately; it does not decode the old flat one. -/
namespace J6R36ChildFramedRoute
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree

def sideWord (b : Bool) : Word 1 := ⟨[b],rfl⟩

def routeWord {w : ℕ} (r : RouteID w) : Word (w+1) :=
  joinKey r.edge (sideWord r.col)

theorem route_word_injective {w : ℕ} : Function.Injective (routeWord (w:=w)) := by
  intro x y h
  have ⟨a,b⟩ := join_key_equality h
  have b' : x.col=y.col := List.cons.inj (congrArg Word.bits b) |>.1
  cases x
  cases y
  congr

theorem same_route_word_same_edge_and_side {E : Type*} {w : ℕ}
    (code : E→Word w) (distinct : Function.Injective code) :
    Function.Injective (fun u : E×Bool=>routeWord ⟨code u.1,u.2⟩) := by
  intro x y e
  have h := route_word_injective e
  exact Prod.ext (distinct (congrArg RouteID.edge h)) (congrArg RouteID.col h)

def carryLane {w key prec page : ℕ} (lane : Lane w key prec page) (nextGroup : Word 6) :
    Meter (PortRow (w+1)×Origin key prec page) :=
  let address := duplicateWord (routeWord lane.id)
  let group := duplicateWord nextGroup
  let h := copyBytes lane.body
  let tag := copyOrigin lane.origin
  ⟨(⟨address.result,group.result,h.result⟩,tag.result),
    address.steps+group.steps+h.steps+tag.steps+7⟩

theorem carry_keeps_body_and_stamp {w key prec page : ℕ} (lane : Lane w key prec page)
    (nextGroup : Word 6) :
    carryLane lane nextGroup=
      ⟨(⟨routeWord lane.id,nextGroup,lane.body⟩,lane.origin),
        (3*(w+1)+4)+22+(3*lane.body.length+1)+originFee key prec page lane.origin.pageKey.isSome+7⟩ := by
  simp only [carryLane,duplicate_word_exact,copy_origin_exact,copyBytes_exact]

#print axioms route_word_injective
#print axioms same_route_word_same_edge_and_side
#print axioms carry_keeps_body_and_stamp
end J6R36ChildFramedRoute
