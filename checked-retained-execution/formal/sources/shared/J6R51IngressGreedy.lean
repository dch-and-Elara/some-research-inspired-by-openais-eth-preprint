import J6R51IngressFreshPlant
import J6R17ModeTapeLayout

/-! The existing paid R11/R14 greedy circuit on the chosen source
graph with source-specific incidence and actual degree, not a
separately supplied packing. This is the optional generic greedy
route, not an equality to the printed special diagonal layout. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat J7R9Compiler J7R10Plant J6OrientedHost J6R10Repack
open J6R12CollisionGreedyStep J6R12CollisionBits J6R12CollisionMenu J6R14LayoutCost J6R17ModeTape
open AOracleMachineTime AOracleMachineTimeTape
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 13200000
noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V] (H : CNF V) (s : DeclaredOrder V)

def oldRoster : List (OrderedOld H) :=
  (List.finRange H.length).map Sum.inl++
    s.roster.flatMap (fun v => List.ofFn (fun k : Fin (orderedVar H v).length =>
      Sum.inr ⟨v,k⟩))

theorem old_roster_all (v : OrderedOld H) : v∈oldRoster H s := by
  cases v with
  | inl i => exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange i))
  | inr q => exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨q.1,s.complete _,List.mem_ofFn.mpr ⟨q.2,rfl⟩⟩)

theorem old_roster_distinct : (oldRoster H s).Nodup := by
  unfold oldRoster
  rw [List.nodup_append']
  refine ⟨(List.nodup_finRange _).map Sum.inl_injective,?_,?_⟩
  · apply List.nodup_flatMap.mpr
    constructor
    · intro v _
      apply List.nodup_ofFn_ofInjective
      intro i j eq
      injection eq with h
      cases h
      rfl
    · apply s.distinct.imp
      intro v w h z hz hq
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hz
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hq
      exact h (congrArg Sigma.fst (Sum.inr.inj (hi.trans hj.symm)))
  · intro z ha hb
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hb
    obtain ⟨k,hk⟩ := List.mem_ofFn.mp hj
    cases hk

def rosterRank : OrderedOld H≃Fin (Fintype.card (OrderedOld H)) :=
  listRanks (oldRoster H s) (old_roster_distinct H s) (old_roster_all H s)

def freshNetwork : Network (Fin (nWires H)) (OrderedOld H) (Fin (nSubdiv H)) :=
  ⟨fun i=>((freshPlant H s).rowPort.symm i).1,
    fun i=>((freshPlant H s).colPort.symm i).1⟩

theorem fresh_network_row_degree (v : OrderedOld H) :
    Nat.card {i : Fin (nWires H) // (freshNetwork H s).row i=v}=orderedDegree H v := by
  let E := (freshPlant H s).rowPort
  let A : {i : Fin (nWires H) // (freshNetwork H s).row i=v}≃
      {p : OrderedPort H // p.1=v} := E.symm.subtypeEquiv (fun _=>Iff.rfl)
  let B : {p : OrderedPort H // p.1=v}≃ Fin (orderedDegree H v) :=
    { toFun := by
        rintro ⟨⟨w,i⟩,hw⟩
        change w=v at hw
        subst w
        exact i
      invFun := fun i=>⟨⟨v,i⟩,rfl⟩
      left_inv := by
        rintro ⟨⟨w,i⟩,hw⟩
        change w=v at hw
        subst w
        rfl
      right_inv := fun _=>rfl }
  exact (Nat.card_congr (A.trans B)).trans (by simp)
theorem fresh_network_col_degree (j : Fin (nSubdiv H)) :
    Nat.card {i : Fin (nWires H) // (freshNetwork H s).col i=j}=2 := by
  let E := (freshPlant H s).colPort
  let A : {i : Fin (nWires H) // (freshNetwork H s).col i=j}≃Bool :=
    { toFun := fun i=>(E.symm i.val).2
      invFun := fun b=>⟨E (j,b),by
        change (E.symm (E (j,b))).1=j
        rw [Equiv.symm_apply_apply]⟩
      left_inv := by
        rintro ⟨i,hi⟩
        apply Subtype.ext
        apply E.symm.injective
        rw [Equiv.symm_apply_apply]
        exact Prod.ext hi.symm rfl
      right_inv := by intro b; change (E.symm (E (j,b))).2=b; rw [Equiv.symm_apply_apply] }
  exact (Nat.card_congr A).trans (by simp)

def freshFormat (a e r c : ℕ)
    (ef : nWires H<2^e) (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c) :
    Format (Fin (nWires H)) (OrderedOld H) (Fin (nSubdiv H)) (Fin a→Fin 64) where
  e := e
  kR := r
  kC := c
  b := 6*a
  rCode := fun v=>(rosterRank H s v).val
  cCode := Fin.val
  aCode := fun u=>bitsValue (coordinateLabel u)
  rInj := fun _ _ eq=>(rosterRank H s).injective (Fin.ext eq)
  cInj := fun _ _ eq=>Fin.ext eq
  aInj := by
    intro x y eq
    apply coordinateLabel_inj
    exact equal_width_inj (by rw [coordinateLabel_len,coordinateLabel_len]) eq
  rFit := fun i=>(rosterRank H s i).isLt.trans_le rf
  cFit := fun i=>i.isLt.trans_le cf
  aFit := fun i=>by rw [←coordinateLabel_len i]; exact bitsValue_lt _
  edgesFit := by simpa using ef
  alphabetFit := by simp [Fintype.card_fun,show (64:ℕ)=2^6 by decide,pow_mul]
  row := (freshNetwork H s).row
  col := (freshNetwork H s).col
  edges := List.finRange (nWires H)
  edgesNodup := List.nodup_finRange _
  edgesAll := List.mem_finRange

theorem fresh_format_label (a e r c : ℕ) (ef : nWires H<2^e)
    (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c)
    (z : Fin a→Fin 64) :
    (freshFormat H s a e r c ef rf cf).label z=coordinateLabel z := by
  apply equal_width_inj
  · change (encodeBits (6*a) (bitsValue (coordinateLabel z))).length=_
    rw [encodeBits_length,coordinateLabel_len]
  · change bitsValue (encodeBits (6*a) (bitsValue (coordinateLabel z)))=_
    exact encodeBits_exact _ _ ((freshFormat H s a e r c ef rf cf).aFit z)

def freshVisits : List (OrderedOld H⊕Fin (nSubdiv H)) :=
  (oldRoster H s).map Sum.inl++(List.finRange (nSubdiv H)).map Sum.inr

theorem fresh_visits_distinct : (freshVisits H s).Nodup := by
  unfold freshVisits
  rw [List.nodup_append']
  refine ⟨(old_roster_distinct H s).map Sum.inl_injective,
    (List.nodup_finRange _).map Sum.inr_injective,?_⟩
  intro x a b
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp a
  obtain ⟨j,_,hj⟩ := List.mem_map.mp b
  cases hj

theorem fresh_visits_all (x : OrderedOld H⊕Fin (nSubdiv H)) :
    x∈freshVisits H s := by
  cases x with
  | inl i => exact List.mem_append_left _ (List.mem_map_of_mem (old_roster_all H s i))
  | inr j => exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange j))

theorem fresh_paid_greedy_packing (a e r c q : ℕ)
    (ef : nWires H<2^e) (rf : Fintype.card (OrderedOld H)≤2^r) (cf : nSubdiv H≤2^c)
    (hq : 0<q) (ha : a≤q) (qf : nWires H<2^q)
    (width : ∀ row∈H,row.length≤4)
    (collision : 2*(J9PrintedSchedule.arrayCard a)^2*4≤nWires H)
    (slots : 2^a*J9PrintedSchedule.arrayCard a≤nWires H) :
    let F := freshFormat H s a e r c ef rf cf
    let raw := F.edges.map (fun u=>
      (encodeBits F.kR (F.rCode (F.row u)),encodeBits F.kC (F.cCode (F.col u))))
    let G := packGreedy a F.e F.kR F.kC F.b q ((freshVisits H s).map F.target) raw
    ∃ P : PhysicalPacking (freshNetwork H s) a (Fin 64),
      ∃ L : LayoutReceipt a P.copies (q+1) (Fintype.card (Fin (nWires H))),
        L.boxes=G.result.boxes ∧ L.copies.bits=G.result.copies ∧ G.steps≤packGreedyCap a q F := by
  let F := freshFormat H s a e r c ef rf cf
  have rr (v : OrderedOld H) : Nat.card {i : Fin (nWires H) // (freshNetwork H s).row i=v}≤4 := by
    rw [fresh_network_row_degree]
    exact ordered_width H 4 width v
  have cc (j : Fin (nSubdiv H)) : Nat.card {i : Fin (nWires H) // (freshNetwork H s).col i=j}≤4 := by
    rw [fresh_network_col_degree]
    decide
  obtain ⟨_,P,L,_,_,box,cp,fee⟩ := paidGreedy_layout_receipt (freshNetwork H s) F rfl rfl rfl
    (fresh_format_label H s a e r c ef rf cf) (freshVisits H s)
    (fresh_visits_distinct H s) (fresh_visits_all H s)
    4 q hq ha (by simpa using qf) rr cc (by simpa using collision) (by simpa using slots)
  exact ⟨P,L,box,cp,fee⟩

#print axioms old_roster_all
#print axioms old_roster_distinct
#print axioms fresh_network_row_degree
#print axioms fresh_network_col_degree
#print axioms fresh_format_label
#print axioms fresh_paid_greedy_packing
end
end J6R51Ingress
