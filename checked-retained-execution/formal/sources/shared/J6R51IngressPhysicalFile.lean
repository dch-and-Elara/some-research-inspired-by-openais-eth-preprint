import J6R51IngressClaimRanks

/-! Reorder the newly produced row legs in *their own* fresh physical
half-rank order and emit every R11 vertex target, including isolated
row visitors. This produces the literal R30 signed record shape too. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R49RootIngress J6R50RootIngress J6R30GeneratedRootLayout
open J7R9Compiler J7R9Subdivision J7R10Plant
open J6R12CollisionGreedyStep
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 17700000
set_option maxRecDepth 3200

def pickPorts {r c d : ℕ} (seats : List (RankedSeed r c d)) :
    List (Word (c+1))→Meter (Option (List (SignedHalfPort r c d)))
  | [] => ⟨some [],2⟩
  | k::ks =>
    let A := findRank k seats
    let T := pickPorts seats ks
    match A.result,T.result with
    | some x,some xs =>
      let B := copySeed x
      ⟨some (B.result::xs),A.steps+T.steps+B.steps+7⟩
    | _,_ => ⟨none,A.steps+T.steps+5⟩

theorem picked_ports_exact {I : Type*} {r c d : ℕ}
    (seats : List (RankedSeed r c d)) (is : List I)
    (key : I→Word (c+1)) (atPort : I→SignedHalfPort r c d)
    (h : ∀ i,(findRank (key i) seats).result=some (atPort i)) :
    (pickPorts seats (is.map key)).result=some (is.map atPort) := by
  induction is with
  | nil => rfl
  | cons i rest ih => simp [pickPorts,h i,ih,seed_copy_exact]

def frameTargets (r c nr nc : ℕ) : Meter (List Target) :=
  let R := indexTape r nr
  let C := indexTape c nc
  ⟨R.result.map (fun k=>Target.row k.val)++C.result.map (fun k=>Target.col k.val),
    R.steps+C.steps+8+nr*(7+4*r)+nc*(7+4*c)⟩

structure PhysicalFrame (r c d : ℕ) where
  targets : List Target
  ports : List (SignedHalfPort r c d)

def buildPhysicalFrame {h d j r c : ℕ} (G : PortRoster h d j) :
    Meter (Option (PhysicalFrame r c d)) :=
  let R := rankRoster (r:=r) (c:=c) G
  let K := indexTape (c+1) (2*G.wires.length)
  let P := pickPorts R.result K.result
  let V := frameTargets r c G.rows.length G.wires.length
  ⟨P.result.map (fun ps=>⟨V.result,ps⟩),R.steps+K.steps+P.steps+V.steps+12⟩

noncomputable section

theorem full_roster_length {A : Type*} [DecidableEq A] [Fintype A] (xs : List A)
    (nd : xs.Nodup) (all : ∀ i,i∈xs) : xs.length=Fintype.card A := by
  simpa using Fintype.card_congr (List.Nodup.getEquivOfForallMemList xs nd all)

variable {V : Type} [DecidableEq V] [Fintype V] (H : CNF V) (s : DeclaredOrder V)
variable {h d j r c : ℕ}

theorem old_roster_length : (oldRoster H s).length=Fintype.card (OrderedOld H) :=
  full_roster_length _ (old_roster_distinct H s) (old_roster_all H s)

theorem wire_order_length : (wireOrder H s).length=nSubdiv H :=
  full_roster_length _ (wire_order_distinct H s) (wire_order_all H s)

theorem ranked_rows_characterization (q : RankedSeed r c d) :
    q∈rankedRows H s ↔ ∃ p : OrderedPort H,rankedOf H s p=q := by
  constructor
  · intro x
    obtain ⟨v,_,e⟩ := List.mem_flatMap.mp x
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp e
    exact ⟨⟨v,j⟩,hj⟩
  · rintro ⟨p,rfl⟩
    exact List.mem_flatMap.mpr ⟨p.1,old_roster_all H s _,List.mem_ofFn.mpr ⟨p.2,rfl⟩⟩

theorem ranked_payload_exact
    (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c)
    (df : ∀ v : OrderedOld H,orderedDegree H v≤2^d) (p : OrderedPort H) :
    (rankedOf H s p).2=
      plantHalfPort (freshPlant H s) (freshCodec H s r c d rf cf df) ((freshPlant H s).rowPort p) := by
  let T := freshPlant H s
  let e := rowHalf H p
  have row : T.rowPort.symm (T.rowPort p)=p := T.rowPort.symm_apply_apply p
  have col : T.colPort.symm (T.rowPort p)=(wireRank H s e.1,e.2) := by
    apply T.colPort.injective
    rw [Equiv.apply_symm_apply]
    change (freshPlant H s).rowPort p=(freshPlant H s).colPort (wireRank H s e.1,e.2)
    rw [fresh_row_transport,fresh_col_transport]
  unfold plantHalfPort
  change (rankedOf H s p).2=(⟨(freshCodec H s r c d rf cf df).rowCode (T.rowPort.symm (T.rowPort p)).1,
    wordAt c (T.colPort.symm (T.rowPort p)).1.val,wordAt d (T.rowPort.symm (T.rowPort p)).2.val,
    (T.colPort.symm (T.rowPort p)).2,flagAt (T.old (T.rowPort.symm (T.rowPort p)).1) (T.rowPort.symm (T.rowPort p)).2⟩ : SignedHalfPort r c d)
  rw [row,col]
  rfl

theorem actual_ranked_port_hit
    (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c)
    (df : ∀ v : OrderedOld H,orderedDegree H v≤2^d) (u : Fin (nWires H)) :
    (findRank (wordAt (c+1) u.val) (rankedRows (r:=r) (c:=c) (d:=d) H s)).result=
      some (plantHalfPort (freshPlant H s) (freshCodec H s r c d rf cf df) u) := by
  let T := freshPlant H s
  let p := T.rowPort.symm u
  let x := plantHalfPort T (freshCodec H s r c d rf cf df) u
  have B : nWires H≤2^(c+1) := by
    rw [twice_subdiv,pow_succ,Nat.mul_comm (2:ℕ) (nSubdiv H)]
    exact Nat.mul_le_mul_right 2 cf
  have e : T.rowPort p=u := T.rowPort.apply_symm_apply u
  have f : rankedOf H s p=(wordAt (c+1) u.val,x) := by
    apply Prod.ext
    · exact congrArg (fun i : Fin (nWires H)=>wordAt (c+1) i.val) e
    · exact (ranked_payload_exact H s rf cf df p).trans (congrArg (plantHalfPort T _) e)
  apply find_rank_exact
  · exact (ranked_rows_characterization H s _).mpr ⟨p,f⟩
  · intro y hy
    obtain ⟨q,hq⟩ := (ranked_rows_characterization H s _).mp hy
    have k : (T.rowPort q).val=u.val :=
      wordAt_rank_inj ((T.rowPort q).isLt.trans_le B) (u.isLt.trans_le B) (congrArg Prod.fst hq)
    have eq : q=p := T.rowPort.injective ((Fin.ext k).trans e.symm)
    exact (congrArg Prod.snd (hq.symm.trans ((congrArg (rankedOf H s) eq).trans f)))

theorem frame_targets_exact (r c a e : ℕ) (hr : 0<r) (hc : 0<c)
    (ef : nWires H<2^e) (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c) :
    (frameTargets r c (oldRoster H s).length (wireOrder H s).length).result=
      (freshVisits H s).map (freshFormat H s a e r c ef rf cf).target := by
  let R := oldRoster H s
  have lc := wire_order_length H s
  have f := (index_tape_exact r R.length hr ((old_roster_length H s).le.trans rf)).1
  have g := (index_tape_exact c (nSubdiv H) hc cf).1
  dsimp only [frameTargets]
  rw [lc,f,g,freshVisits]
  simp only [List.map_append,List.map_ofFn,List.map_map]
  apply congrArg₂ List.append
  · have D : List.ofFn R.get=R := List.ofFn_get _
    let fRow : OrderedOld H→Target := (freshFormat H s a e r c ef rf cf).target ∘ Sum.inl
    have eq : R.map fRow=List.ofFn (fRow ∘ R.get) := by
      rw [←List.map_ofFn,D]
    change _=R.map fRow
    rw [eq]
    apply congrArg List.ofFn
    funext k
    change Target.row (encodeBits r k.val)=Target.row (encodeBits r ((rosterRank H s) (R.get k)).val)
    rw [rank_at_roster_index H s k]
  · have D : List.finRange (nSubdiv H)=List.ofFn (fun k : Fin (nSubdiv H)=>k) := by
      apply List.ext_getElem
      · simp
      · intro k hk hl
        apply Fin.ext
        simp
    rw [D,List.map_ofFn]
    rfl

theorem frame_on_legal_roster {h d j r c : ℕ}
    (code : V→List Bool) (inj : Function.Injective code)
    (fitH : H.length≤2^h) (fitD : ∀ row∈H,row.length≤2^d)
    (fitJ : ∀ v,(occurrences H v).length-3≤2^j)
    (a e : ℕ) (hr : 0<r) (hc : 0<c) (hd : 0<d)
    (ef : nWires H<2^e) (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c)
    (df : ∀ v : OrderedOld H,orderedDegree H v≤2^d) :
    (buildPhysicalFrame (r:=r) (c:=c) (⟨rawWires (h:=h) (d:=d) (j:=j) H s code,
      (oldRoster H s).map (rowSeeds H code)⟩ : PortRoster h d j)).result=
      some ⟨(freshVisits H s).map (freshFormat H s a e r c ef rf cf).target,
        List.ofFn (plantHalfPort (freshPlant H s) (freshCodec H s r c d rf cf df))⟩ := by
  have L : (rawWires (h:=h) (d:=d) (j:=j) H s code).length=nSubdiv H := by
    rw [rawWires,List.length_map,wire_order_length]
  have B : nWires H≤2^(c+1) := by
    rw [twice_subdiv,pow_succ,Nat.mul_comm (2:ℕ) (nSubdiv H)]
    exact Nat.mul_le_mul_right 2 cf
  have rEq := rank_true_roster_exact H s code inj fitH fitD fitJ hc
    ((wire_order_length H s).le.trans cf) hd df hr ((old_roster_length H s).le.trans rf)
  have t := (index_tape_exact (c+1) (nWires H) (by omega) B).1
  have g := frame_targets_exact H s r c a e hr hc ef rf cf
  have W := picked_ports_exact (rankedRows H s)
    (List.ofFn (fun i : Fin (nWires H)=>i)) (fun i=>wordAt (c+1) i.val)
    (plantHalfPort (freshPlant H s) (freshCodec H s r c d rf cf df)) (actual_ranked_port_hit H s rf cf df)
  simp only [List.map_ofFn,Function.comp_def] at W
  dsimp only [buildPhysicalFrame]
  rw [rEq,L,←twice_subdiv H,t,W,List.length_map]
  rw [wire_order_length H s] at g
  rw [g]
  rfl

#print axioms picked_ports_exact
#print axioms full_roster_length
#print axioms old_roster_length
#print axioms wire_order_length
#print axioms ranked_rows_characterization
#print axioms ranked_payload_exact
#print axioms actual_ranked_port_hit
#print axioms frame_targets_exact
#print axioms frame_on_legal_roster
end
end J6R51Ingress
