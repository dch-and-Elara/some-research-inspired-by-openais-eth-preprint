import J6R32ChildResidentTransferFormat
import J6R32ChildResidentTransferSeat

/-! A paid single literal child, not the old noncomputable layout choice.
Its preinstalled parent vertex-key words include isolated old factors and
unused parent packets. The child incidence, targets, selected labels,
copy word, orientation bank and mode list are all computed. -/
namespace J6R32ChildResidentTransfer
open scoped Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape
open J6R10Repack P11FullPacking J6R11Blueprint J6R9PacketScopes
open J6R15ModeCost J6R26DescriptorTree J6R27OriginalGate J6R17ModeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionMenu J6R14LayoutCost
set_option maxHeartbeats 17000000
set_option maxRecDepth 2400

def literalChildRun {r k e w p : ℕ} (a q i : ℕ) (group : Word 6)
    (parent : List (ParentHalfWord r k e w p)) (rows : List (Word r)) (pages : List (Word k))
    (precision : Word (q+1)) : Meter (List (ChildLane r k e w p)×GreedyRosterInput q) :=
  let ports := transferChild group parent
  let es := mapMeter rawLane ports.result
  let ts := writeTargets rows pages
  let core := buildGreedyResident a q r k (6*a) q i ts.result es.result precision
  ⟨(ports.result,core.result),ports.steps+es.steps+ts.steps+core.steps+6⟩

section Physical
variable {E A B : Type} [Fintype E] [Fintype A] [Fintype B] {N : Network E A B}
variable {a r w e b : ℕ} (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (g : Fin 64)
variable (ownerKey : A⊕B→Word r) (ownerInj : Function.Injective ownerKey)
variable (copyFit : P.copies≤2^w)
variable (id : E→Word e) (stamp : A⊕B→Stamp b w)
variable (order : List (Port E)) (unique : order.Nodup) (all : ∀ u,u∈order)
local notation "CNet" => child N (atGroup P i) (atPacket P) g
local notation "RType" => Old (atGroup P i) g
local notation "PType" => Page a P.copies (Fin 64)
local notation "CEdge" => ChildEdge N (atGroup P i) g
local notation "CK" => childPageKey w

theorem literal_child_resident_roster
    (raw : List (ParentHalfWord r (w+13*a) e b w))
    (install : raw=order.map (installedHalf P i ownerKey CK id stamp))
    (olds : List RType) (nd : olds.Nodup) (full : ∀ x,x∈olds)
    (oldKeys : List (Word r)) (pageKeys : List (Word (w+13*a)))
    (ok : oldKeys=olds.map (fun x=>ownerKey x.val))
    (pk : pageKeys=(orderedChildPages a P.copies).map CK)
    (a' q Δ : ℕ) (hq : 0<q) (ha : a'≤q) (fit : Fintype.card CEdge<2^q)
    (hr : ∀ v,Nat.card {x : CEdge // (CNet).row x=v}≤Δ)
    (hc : ∀ v,Nat.card {x : CEdge // (CNet).col x=v}≤Δ)
    (collision : 2*(J9PrintedSchedule.arrayCard a')^2*Δ≤Nat.card CEdge)
    (slots : 2^a'*J9PrintedSchedule.arrayCard a'≤Nat.card CEdge)
    (j : Fin a') (pr : Word (q+1)) (positive : 0<pr.val) :
    let C := CNet
    let ch := childLaneOrder P i g order
    let h := child_lane_order_complete P i g order unique all
    let F := childFormat (a:=a') C q fit ch h.1 h.2 (fun x=>ownerKey x.val) CK
      (ownerInj.comp Subtype.val_injective) (child_page_key_injective w copyFit)
    let out := literalChildRun a' q j.val (word g.val) raw oldKeys pageKeys pr
    out.result.1=ch.map (fun x=>⟨ownerKey (C.row x).val,CK (C.col x),id (edge x.val),
      side x.val,stamp (C.row x).val⟩) ∧
    ∃ L : PhysicalPacking C a' (Fin 64), L.mask=childMask a' L.copies ∧
      out.result.2.copies.val=L.copies ∧
      out.result.2.masks=(orderedChildPages a' L.copies).map (encodeMaskRow L.mask) ∧
      (∃ ms : List (PacketMode j L.copies (2^(j.val+1)) pr.val),
        ms.Nodup ∧ (∀ m,m∈ms) ∧ out.result.2.roster.modes=ms.map (encodeMode j) ∧
        out.result.2.roster.modes.Nodup ∧ out.result.2.roster.weights.map Word.val=ms.map modeWeight ∧
        out.result.2.roster.precision=pr) ∧
      out.steps≤transferFee r (w+13*a) e b w order.length ch.length+
        (3*r+3*(w+13*a)+17)*ch.length+(6*r+22)*olds.length+
        (3*(w+13*a)+13)*(orderedChildPages a P.copies).length+4+
        greedyResidentFee F q j.val L.copies pr.val+6 := by
  let C := CNet
  let ch := childLaneOrder P i g order
  let h := child_lane_order_complete P i g order unique all
  let rr : RType→Word r := fun x=>ownerKey x.val
  have ri : Function.Injective rr := ownerInj.comp Subtype.val_injective
  have ci : Function.Injective (CK : PType→Word (w+13*a)) := child_page_key_injective w copyFit
  let F := childFormat (a:=a') C q fit ch h.1 h.2 rr CK ri ci
  let pg := orderedChildPages a P.copies
  let vs := olds.map (Sum.inl : RType→RType⊕PType) ++ pg.map (Sum.inr : PType→RType⊕PType)
  have vsN : vs.Nodup := by
    apply List.Nodup.append
    · exact nd.map Sum.inl_injective
    · exact (child_pages_complete _ _).1.map Sum.inr_injective
    · intro x hx hy
      obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
      obtain ⟨k,_,bad⟩ := List.mem_map.mp hy
      cases bad
  have vsAll (x : RType⊕PType) : x∈vs := by
    cases x with
    | inl v => exact List.mem_append_left _ (List.mem_map.mpr ⟨v,full v,rfl⟩)
    | inr v => exact List.mem_append_right _ (List.mem_map.mpr ⟨v,(child_pages_complete _ _).2.1 v,rfl⟩)
  let L := transferChild (word g.val) raw
  obtain ⟨ln,lf⟩ := installed_transfer_physical P i g ownerKey CK id stamp order raw install
  let I := mapMeter rawLane L.result
  obtain ⟨ins,ic⟩ := raw_lanes_exact L.result
  have Lcount : L.result.length=ch.length := by rw [ln,List.length_map]
  rw [Lcount] at ic
  have insE : I.result=F.edges.map (fun x=>
      (encodeBits F.kR (F.rCode (F.row x)),encodeBits F.kC (F.cCode (F.col x)))) := by
    change (mapMeter rawLane L.result).result=_
    rw [ins,ln,List.map_map]
    change _=ch.map _
    apply List.map_congr_left
    intro x _
    have A := congrArg Word.bits (valued_word (rr (C.row x)))
    have B := congrArg Word.bits (valued_word (CK (C.col x)))
    exact Prod.ext A.symm B.symm
  let Ts := writeTargets oldKeys pageKeys
  obtain ⟨te,tf⟩ := typed_target_tape (a:=a') C q fit ch h.1 h.2 rr CK ri ci olds pg
  have Te : Ts.result=vs.map F.target := by unfold Ts; rw [ok,pk]; exact te
  have Tf : Ts.steps≤(6*r+22)*olds.length+(3*(w+13*a)+13)*pg.length+4 := by
    unfold Ts
    rw [ok,pk]
    exact tf
  obtain ⟨P',pm,cp,bm,roster,gf⟩ := paid_greedy_child_roster C F rfl rfl rfl
    (child_format_label C q fit ch h.1 h.2 rr CK ri ci)
    vs vsN vsAll Δ q hq ha fit hr hc collision slots j pr positive
  let D := buildGreedyResident a' q r (w+13*a) (6*a') q j.val Ts.result I.result pr
  have eq :
      D=buildGreedyResident a' F.e F.kR F.kC F.b q j.val (vs.map F.target)
        (F.edges.map (fun x=>(encodeBits F.kR (F.rCode (F.row x)),
          encodeBits F.kC (F.cCode (F.col x))))) pr := by
    unfold D
    rw [Te,insE]
    rfl
  refine ⟨ln, P',pm, ?_,?_,?_,?_⟩
  · change D.result.copies.val=P'.copies
    rw [eq]
    exact cp
  · change D.result.masks=_
    rw [eq]
    exact bm
  · change ∃ _ms : List (PacketMode j P'.copies (2^(j.val+1)) pr.val), _
    rw [show (literalChildRun a' q j.val (word g.val) raw oldKeys pageKeys pr).result.2 = D.result from rfl,eq]
    exact roster
  · change L.steps+I.steps+Ts.steps+D.steps+6≤_
    have hD : D.steps≤greedyResidentFee F q j.val P'.copies pr.val := by rw [eq]; exact gf
    change L.steps=transferFee r (w+13*a) e b w order.length ch.length at lf
    change I.steps≤_ at ic
    rw [lf]
    nlinarith only [ic,Tf,hD]
end Physical

#print axioms literal_child_resident_roster
end J6R32ChildResidentTransfer