import J6R33GeneratedChildSiteSparse

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2500
set_option maxHeartbeats 14500000

/-! The R32 full runtime result, not an arbitrary selected packing,
provides a concrete resident receipt. The target is the physical
descendant made by one actual parent group, including its ancestry
stamps and all ordered padded packet copies. -/
namespace J6R33GeneratedChildSite
open scoped Polynomial Classical
open AOracleMachineTime J6R10Repack P11FullPacking J6R11Blueprint J6R9PacketScopes
open J6R15ModeCost J6R26DescriptorTree J6R27OriginalGate J6R17ModeTape
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionMenu J6R14LayoutCost
open J6R32ChildResidentTransfer J6R31RootResidentTables

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

theorem literal_child_produces_receipt
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
    (j : Fin a') (axis : List Bool) (clock : axis.length=j.val)
    (pr : Word (q+1)) (positive : 0<pr.val) :
    let C := CNet
    let ch := childLaneOrder P i g order
    let h := child_lane_order_complete P i g order unique all
    let F := childFormat (a:=a') C q fit ch h.1 h.2 (fun x=>ownerKey x.val) CK
      (ownerInj.comp Subtype.val_injective) (child_page_key_injective w copyFit)
    let out := literalChildFullRun a' q j.val axis (word g.val) raw oldKeys pageKeys pr
    out.result.1=ch.map (fun x=>⟨ownerKey (C.row x).val,CK (C.col x),id (edge x.val),
      side x.val,stamp (C.row x).val⟩) ∧
    ∃ L : PhysicalPacking C a' (Fin 64),
      Nonempty (ResidentReceipt L j pr.val out.result.2) ∧ L.mask=childMask a' L.copies ∧
      out.steps≤transferFee r (w+13*a) e b w order.length ch.length+
        (3*r+3*(w+13*a)+17)*ch.length+(6*r+22)*olds.length+
        (3*(w+13*a)+13)*(orderedChildPages a P.copies).length+4+
        fullGreedyFee F q j.val L.copies pr.val+6 := by
  obtain ⟨lanes,L,Es,hN,hAll,hM,hCopy,hSeat,hRawCopies,hMask,hR,hFee⟩ :=
    literal_child_full_residents P i g ownerKey ownerInj copyFit id stamp order unique all raw
      install olds nd full oldKeys pageKeys ok pk a' q Δ hq ha fit hr hc collision slots j axis clock
      pr positive
  obtain ⟨ms,nd,complete,hE,nE,wE,pE⟩ := hR
  have ed : Es.length=Fintype.card CEdge := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (rosterIndex Es hN hAll)
  exact ⟨lanes,L,⟨⟨Es,hN,hAll,ed.symm ▸ fit,hCopy,hRawCopies,hSeat,hMask,ms,
    nd,complete,hE,nE,wE,congrArg Word.val pE⟩⟩,hM,hFee⟩

#print axioms literal_child_produces_receipt
end J6R33GeneratedChildSite
