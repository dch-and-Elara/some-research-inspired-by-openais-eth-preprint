import J6R51IngressPortRows
import J6R51IngressHalfRank

/-! At every actual old-row leg compute the subdivision and half
ranks by a charged raw lookup, and write the independent row/leg
counters and genuine sign.  No precomputed signed port is passed in. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime J6R49RootIngress J6R50RootIngress
open J7R9Compiler J7R9Subdivision J7R10Plant J6R30GeneratedRootLayout
open J6R12CollisionEdges
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16400000
set_option maxRecDepth 3100

abbrev RankedSeed (r c d : ℕ) := Word (c+1)×SignedHalfPort r c d

def rankPort {h d j r c : ℕ} (wires : List (WireKey h d j))
    (row : Word r) (leg : Word d) (z : PortSeed h d j) : Meter (Option (RankedSeed r c d)) :=
  let K := seekWire z.key (wordOne c) (wordAt c 0) wires
  match K.result with
  | none => ⟨none,K.steps+6*c+8⟩
  | some col =>
    let fields := copySeed (⟨row,col,leg,z.side,z.flag⟩ : SignedHalfPort r c d)
    ⟨some (sideWord z.side col,fields.result),K.steps+fields.steps+10*c+14⟩

def rankRow {h d j r c : ℕ} (wires : List (WireKey h d j)) (row : Word r)
    (ports : List (PortSeed h d j)) : Meter (List (RankedSeed r c d)) :=
  let P := indexTape d ports.length
  let lanes := ports.zipWith (fun s k=>(s,k)) P.result
  let Y := mapMeter (fun z=>rankPort (c:=c) wires row z.2 z.1) lanes
  ⟨Y.result.filterMap id,P.steps+Y.steps+7+lanes.length*(9+4*(r+c+d))⟩

def rankRoster {h d j r c : ℕ} (G : PortRoster h d j) : Meter (List (RankedSeed r c d)) :=
  let R := indexTape r G.rows.length
  let aligned := G.rows.zipWith (fun ps row=>(ps,row)) R.result
  let A := mapMeter (fun z=>rankRow (c:=c) G.wires z.2 z.1) aligned
  ⟨A.result.flatten,R.steps+A.steps+7+4*(G.rows.length+A.result.flatten.length)⟩

theorem paid_map_result {A B : Type*} (f : A→Meter B) (xs : List A) :
    (mapMeter f xs).result=xs.map (fun x=>(f x).result) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapMeter,ih]

theorem port_rank_fee {h d j r c : ℕ} (wires : List (WireKey h d j))
    (row : Word r) (leg : Word d) (z : PortSeed h d j) (W : ℕ)
    (fit : ∀ u∈wires,keyWidth u≤W) :
    (rankPort (c:=c) wires row leg z).steps≤
      2+wires.length*(17+5*W+12*c)+seedFee r c d+10*c+14 := by
  have e := seek_wire_fee z.key (wordOne c) (wordAt c 0) wires W fit
  dsimp only [rankPort]
  cases K : (seekWire z.key (wordOne c) (wordAt c 0) wires).result with
  | none => simp only [K]; omega
  | some w => simp only [K,seed_copy_exact]; omega

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V] (H : CNF V) (s : DeclaredOrder V)
variable {h d j r c : ℕ} (code : V→List Bool)

def rawWires : List (WireKey h d j) := (wireOrder H s).map (keyOf H code)

def rankedOf (p : OrderedPort H) : RankedSeed r c d :=
  let e := rowHalf H p
  (wordAt (c+1) ((freshPlant H s).rowPort p).val,
    ⟨wordAt r ((rosterRank H s) p.1).val,wordAt c ((wireRank H s) e.1).val,
      wordAt d p.2.val,e.2,flagAt (orderedGate H p.1) p.2⟩)

theorem rank_port_exact (inj : Function.Injective code)
    (fitH : H.length≤2^h) (fitD : ∀ row∈H,row.length≤2^d)
    (fitJ : ∀ v,(occurrences H v).length-3≤2^j)
    (hc : 0<c) (fitC : (wireOrder H s).length≤2^c) (p : OrderedPort H) :
    (rankPort (c:=c) (rawWires (h:=h) (d:=d) (j:=j) H s code)
      (wordAt r ((rosterRank H s) p.1).val) (wordAt d p.2.val)
      (seatOf H code p)).result=some (rankedOf (r:=r) H s p) := by
  let e := rowHalf H p
  have K := raw_wire_rank_from_chosen_list (h:=h) (d:=d) (j:=j) H s code inj fitH fitD fitJ hc fitC e.1
  change (seekWire (keyOf H code e.1) (wordOne c) (wordAt c 0)
    (rawWires (h:=h) (d:=d) (j:=j) H s code)).result=_ at K
  dsimp only [rankPort,seatOf,rankedOf]
  rw [show rowHalf H p=e by rfl,K]
  simp only [seed_copy_exact,side_word_exact]
  rw [fresh_row_transport]
  have E : (e.1,e.2)=e := Prod.eta e
  rw [←E,half_rank_pair]

theorem rank_row_exact (inj : Function.Injective code)
    (fitH : H.length≤2^h) (fitD : ∀ row∈H,row.length≤2^d)
    (fitJ : ∀ v,(occurrences H v).length-3≤2^j)
    (hc : 0<c) (fitC : (wireOrder H s).length≤2^c)
    (hd : 0<d) (width : ∀ v : OrderedOld H,orderedDegree H v≤2^d)
    (v : OrderedOld H) :
    (rankRow (c:=c) (rawWires (h:=h) (d:=d) (j:=j) H s code)
      (wordAt r ((rosterRank H s) v).val) (rowSeeds H code v)).result=
      List.ofFn (fun k : Fin (orderedDegree H v)=>rankedOf H s ⟨v,k⟩) := by
  let f := fun k : Fin (orderedDegree H v)=>rankedOf (d:=d) (r:=r) (c:=c) H s ⟨v,k⟩
  have l := (index_tape_exact d (orderedDegree H v) hd (width v)).1
  dsimp only [rankRow,rowSeeds]
  rw [List.length_ofFn,l,zip_ofFn_exact,paid_map_result,List.map_ofFn]
  have e : ((fun z : PortSeed h d j×Word d=>(rankPort (c:=c) (rawWires H s code)
      (wordAt r ((rosterRank H s) v).val) z.2 z.1).result) ∘
      fun k : Fin (orderedDegree H v)=>(seatOf H code ⟨v,k⟩,wordAt d k.val))=some ∘ f := by
    funext k
    exact rank_port_exact H s code inj fitH fitD fitJ hc fitC ⟨v,k⟩
  rw [e,←List.map_ofFn,List.filterMap_map]
  simp [Function.comp_def,f]

theorem rank_at_roster_index (k : Fin (oldRoster H s).length) :
    ((rosterRank H s) ((oldRoster H s).get k)).val=k.val := by
  rw [rosterRank,list_rank_value]
  exact List.idxOf_getElem (old_roster_distinct H s) k.val k.isLt

def rankedRows : List (RankedSeed r c d) :=
  (oldRoster H s).flatMap (fun v=>List.ofFn (fun k : Fin (orderedDegree H v)=>
    rankedOf H s ⟨v,k⟩))

theorem rank_true_roster_exact (inj : Function.Injective code)
    (fitH : H.length≤2^h) (fitD : ∀ row∈H,row.length≤2^d)
    (fitJ : ∀ v,(occurrences H v).length-3≤2^j)
    (hc : 0<c) (fitC : (wireOrder H s).length≤2^c) (hd : 0<d)
    (width : ∀ v : OrderedOld H,orderedDegree H v≤2^d)
    (hr : 0<r) (fitR : (oldRoster H s).length≤2^r) :
    (rankRoster (r:=r) (c:=c) (⟨rawWires (h:=h) (d:=d) (j:=j) H s code,
      (oldRoster H s).map (rowSeeds H code)⟩ : PortRoster h d j)).result=rankedRows H s := by
  let t := oldRoster H s
  have e0 : List.ofFn t.get=t := List.ofFn_get t
  have e1 := (index_tape_exact r t.length hr fitR).1
  have erows : t.map (rowSeeds (d:=d) (h:=h) (j:=j) H code)=
      List.ofFn (rowSeeds H code ∘ t.get) := by rw [←List.map_ofFn,e0]
  dsimp only [rankRoster]
  rw [List.length_map,e1,erows,zip_ofFn_exact,paid_map_result,List.map_ofFn]
  have ef : (fun z : List (PortSeed h d j)×Word r=>
      (rankRow (c:=c) (rawWires H s code) z.2 z.1).result) ∘
      (fun k : Fin t.length=>(rowSeeds H code (t.get k),wordAt r k.val)) =
      (fun k : Fin t.length=>List.ofFn (fun i : Fin (orderedDegree H (t.get k))=>
        rankedOf (d:=d) (r:=r) (c:=c) H s ⟨t.get k,i⟩)) := by
    funext k
    have e := rank_row_exact (r:=r) H s code inj fitH fitD fitJ hc fitC hd width (t.get k)
    rw [rank_at_roster_index H s k] at e
    exact e
  simp only [Function.comp_def] at ef ⊢
  rw [ef]
  let Q := fun v : OrderedOld H=>List.ofFn (fun i : Fin (orderedDegree H v)=>
    rankedOf (d:=d) (r:=r) (c:=c) H s ⟨v,i⟩)
  change (List.ofFn (Q ∘ t.get)).flatten=(t.map Q).flatten
  rw [←List.map_ofFn,e0]

#print axioms paid_map_result
#print axioms port_rank_fee
#print axioms rank_port_exact
#print axioms rank_row_exact
#print axioms rank_at_roster_index
#print axioms rank_true_roster_exact
end
end J6R51Ingress
