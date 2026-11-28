import J6R68CanonicalRootWriterOrder

/-! The exterior Page syntax is recovered from the bank that was
really emitted. No request list or route trace is an executable input:
physical page/port predicates and trace transport are proofs about
the measured selectors. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R55BootBodies J6R48RawRoute J6R50SourceProducer J6R54ExteriorOwner
open J6R53OldOwner J6R62Leaf J6R50Leaf J6R52Terminal J6R53TerminalGate
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000
set_option maxRecDepth 4500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw own : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => (exteriorChild G ell X.centre X.sample X.group).host.Edge
local notation "U" => (Vertex (exteriorChild G ell X.centre X.sample X.group))
local notation "Col" => (exteriorChild G ell X.centre X.sample X.group).host.Col

abbrev pageCol (k : CanonicalPage m) : Col := canonicalPageEquiv G ell X.centre k

abbrev pagePoint (k : CanonicalPage m) : Point f ell :=
  atVertex Ext (.inr (pageCol X k))

def emittedPageTrace (k : CanonicalPage m) : Trace (stableBorn X k) (pagePoint X k) :=
  Eq.mp (congrArg (Trace (stableBorn X k)) (stable_exterior_exact_born X k).symm)
    (Trace.start : Trace (stableBorn X k) (stableBorn X k))

private theorem start_depth_transport {F : ℤ[X]} {v : ℕ} {p q : Point F v} (e : p=q) :
    (Eq.mp (congrArg (Trace q) e.symm) (Trace.start : Trace q q)).depth=0 := by
  cases e
  rfl

private theorem start_literal_transport {F : ℤ[X]} {v : ℕ} {p q : Point F v}
    (e : p=q) (seed : PortAt q→List Bool) (x : PortAt p) :
    (Eq.mp (congrArg (Trace q) e.symm) (Trace.start : Trace q q)).literal seed x=
      seed (castPort e x) := by
  cases e
  rfl


theorem emitted_page_route_depth_is_zero (k : CanonicalPage m) :
    (emittedPageTrace X k).depth=0 :=
  start_depth_transport (stable_exterior_exact_born X k)

theorem emitted_packet_seed_is_same_frame (name : U→Word own)
    (k : CanonicalPage m) (x : PortAt (pagePoint X k)) :
    let row := exteriorFrameAt X gate pad name (edge x.val)
    row.right.origin=exteriorPageOrigin X pad k ∧
      row.right.body=(emittedPageTrace X k).literal (originSeed (rootChart P) (oddAxis m) X.group k) x := by
  let eq := stable_exterior_exact_born X k
  let y := castPort eq x
  let actual := (actualLane X gate pad (edge y.val).val).packet
  have h : (edge y.val).val=(edge x.val).val := canonical_exterior_cast_keeps_wire X k x
  obtain ⟨_,body,stamp,_,_,pg,_⟩ := actual_exterior_packet_seed X gate pad k y
  have origin : actual.origin=exteriorPageOrigin X pad k := by
    change Origin.mk actual.origin.stamp actual.origin.pageKey=_
    exact congrArg₂ Origin.mk stamp pg
  let seed := originSeed (rootChart P) (oddAxis m) X.group k
  have bodyEq : (emittedPageTrace X k).literal seed x=seed y :=
    start_literal_transport eq seed x
  change
    (actualLane X gate pad (edge x.val).val).packet.origin=exteriorPageOrigin X pad k ∧
    (actualLane X gate pad (edge x.val).val).packet.body=(emittedPageTrace X k).literal seed x
  rw [←h,bodyEq]
  exact ⟨origin,body⟩

def rightAt (c : Col) (e : E) (h : (Ext).host.network.col e=c) : PortAt (atVertex Ext (.inr c)) :=
  ⟨.inr e,congrArg Sum.inr h⟩

def orderedPagePorts (k : CanonicalPage m) : List (PortAt (pagePoint X k)) :=
  (scanSubtype (fun e : E=>(Ext).host.network.col e=pageCol X k)
    (orderedExteriorEdges X)).map (fun x=>rightAt X (pageCol X k) x.val x.property)

theorem all_page_ports_in_physical_order (k : CanonicalPage m) (x : PortAt (pagePoint X k)) :
    x∈orderedPagePorts X k := by
  obtain ⟨e,h⟩ := x
  cases e with
  | inl e => cases h
  | inr e =>
    let g : {u : E // (Ext).host.network.col u=pageCol X k} :=
      ⟨e,Sum.inr.inj h⟩
    refine List.mem_map.mpr ⟨g,?_ ,rfl⟩
    exact (scan_subtype_mem _ _ g).mpr ((reviewed_exterior_order X).2 e)

theorem right_page_key_is_literal_column (name : U→Word own)
    (gateWidth : gate.created.val=base) (e : E) :
    (exteriorFrameAt X gate pad name e).right.origin.pageKey=
      some (bootPageKey X pad ((Ext).host.network.col e)) := by
  let c := (Ext).host.network.col e
  let x := rightAt X c e rfl
  have h := congrArg Origin.pageKey (exact_real_root_tag_at_port X gate pad gateWidth (.inr c) x)
  exact h

theorem actual_root_packet_scan (name : U→Word own) (gateWidth : gate.created.val=base)
    (k : CanonicalPage m) :
    let target := bootPageKey X pad (pageCol X k)
    (scanFresh target (trueFrames X gate pad name)).result=
      (orderedPagePorts X k).map (fun x=>requestView (exteriorFrameAt X gate pad name (edge x.val)).right) := by
  let c := pageCol X k
  let K := bootPageKey X pad c
  change (scanFresh K (trueFrames X gate pad name)).result=_
  rw [scan_fresh_exact]
  dsimp only [trueFrames,orderedPagePorts,scanSubtype]
  rw [List.filterMap_map,List.map_map,List.map_filterMap]
  apply List.filterMap_congr
  intro e _
  have real := right_page_key_is_literal_column X gate pad name gateWidth e
  have test : (cmpAddr K (bootPageKey X pad ((Ext).host.network.col e))).result=true ↔
      (Ext).host.network.col e=c := by
    rw [(cmpAddr_exact _ _).1,(boot_page_key_injective X pad).eq_iff,eq_comm]
  by_cases h : (Ext).host.network.col e=pageCol X k
  · have yes := test.mpr h
    simp only [Function.comp_apply,chooseFresh,real,yes,if_true,dif_pos h,Option.map_some]
    rfl
  · have no : (cmpAddr K (bootPageKey X pad ((Ext).host.network.col e))).result=false :=
      Bool.eq_false_iff.mpr (fun H=>h (test.mp H))
    simp only [Function.comp_apply,chooseFresh,real,no,Bool.false_eq_true,if_false,dif_neg h,Option.map_none]

#print axioms emitted_page_route_depth_is_zero
#print axioms emitted_packet_seed_is_same_frame
#print axioms all_page_ports_in_physical_order
#print axioms right_page_key_is_literal_column
#print axioms actual_root_packet_scan
end
end J6R68CanonicalRootWriter

