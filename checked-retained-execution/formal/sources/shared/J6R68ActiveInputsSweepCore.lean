import J6R68ActiveInputsBaseCurrent
import J6R68ActiveInputsBaseCentre

/-! A real recursive fold consumes the raw emitted centre table in its
own order. The dependent membership arguments are proofs, with no
search or typed-to-bytes re-encoding in the sweep. -/
namespace J6R68ActiveInputs.Sweep
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R23ScheduleWeight J6R24MeteredRecursion J6R49DFS

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 3600
set_option maxSynthPendingDepth 12
set_option Elab.async false

section Fold
variable {α X : Type*} {p ell : ℕ} {fw : List (A1R10.Word p)} {Valid : α → Prop}

def sumRaw (hp : 0<p) (emit : ∀ x, Valid x → Meter (UVBlock fw ell)) :
    (raw : List α) → (∀ x∈raw,Valid x) → Meter (UVBlock fw ell)
  | [],_ => zeroM hp
  | x::xs,ok =>
    addM hp (emit x (ok x List.mem_cons_self))
      (sumRaw hp emit xs (fun i hi=>ok i (List.mem_cons_of_mem _ hi)))

theorem raw_fold_meter_is_in_the_emission_order (hp : 0<p)
    (emit : ∀ x, Valid x → Meter (UVBlock fw ell))
    (tag : ∀ x,Valid x → X) (run : X → Meter (UVBlock fw ell))
    (raw : List α) (ok : ∀ x∈raw,Valid x)
    (rowEq : ∀ x (hx : Valid x),emit x hx=run (tag x hx)) :
    sumRaw hp emit raw ok=sumM hp run (raw.pmap tag ok) := by
  induction raw with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumRaw,List.pmap_cons,sumM,rowEq,ih]
end Fold

noncomputable section
variable {f : ℤ[X]} {ell s q : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth)
local notation "U" => (Shape.levelWidth (printedParams (f:=f) (ell:=ell) s) c.depth)

def centreFor {rows : List (RawCentre q)} (C : StockTapeCorrect A c.edges U rows)
    (x : RawCentre q) (live : x∈rows) : Center S c :=
  ⟨offsetCentre A x.key,by
    change offsetCentre A x.key∈active A c.edges U
    rw [←C.complete,List.mem_toFinset]
    exact List.mem_map_of_mem live⟩

structure Schedule (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (bank : Bank f) (q : ℕ) where
  stock : RawBaseStock q
  roster : StockTapeCorrect A c.edges U stock.rows
  marginExact : bitsValue stock.margin.val=commonLoss A c.edges U
  centre (x : RawCentre q) (live : x∈stock.rows) : CentreMachine sel d (centreFor roster x live) bank q

variable (D : Schedule sel d bank q)

abbrev Schedule.EmitRow := {x : RawCentre q // x∈D.stock.rows}

def Schedule.tag (x : D.EmitRow) : Center S c := centreFor D.roster x.val x.property

theorem Schedule.tag_inj : Function.Injective D.tag := by
  intro x y eq
  apply Subtype.ext
  exact List.inj_on_of_nodup_map D.roster.distinct x.property y.property (congrArg Subtype.val eq)

theorem Schedule.tag_surj : Function.Surjective D.tag := by
  intro t
  have once : t.val ∈ (D.stock.rows.map (fun x=>offsetCentre A x.key)).toFinset := by
    rw [D.roster.complete]
    exact t.property
  rw [List.mem_toFinset] at once
  obtain ⟨x,hx,h⟩ := List.mem_map.mp once
  exact ⟨⟨x,hx⟩,Subtype.ext h⟩

def Schedule.centresView : List (Center S c) :=
  D.stock.rows.pmap (fun x hx=>D.tag ⟨x,hx⟩) (fun _ hx=>hx)

theorem Schedule.centres_in_order :
    D.centresView.map Subtype.val=D.stock.rows.map (fun x=>offsetCentre A x.key) := by
  rw [Schedule.centresView,List.map_pmap]
  change D.stock.rows.pmap (fun (x : RawCentre q) (_ : x∈D.stock.rows)=>offsetCentre A x.key)
    (fun _ hx=>hx)=_
  exact List.pmap_eq_map _

theorem Schedule.centres_unique : D.centresView.Nodup :=
  List.Nodup.of_map Subtype.val (D.centres_in_order.symm ▸ D.roster.distinct)

theorem Schedule.centres_complete (t : Center S c) : t∈D.centresView := by
  obtain ⟨⟨x,hx⟩,ht⟩ := D.tag_surj t
  unfold Schedule.centresView
  rw [←ht]
  exact List.mem_pmap_of_mem hx

def Schedule.proofRow (t : Center S c) : D.EmitRow := Classical.choose (D.tag_surj t)

theorem Schedule.proofRow_key (t : Center S c) : D.tag (D.proofRow t)=t :=
  Classical.choose_spec (D.tag_surj t)

def Schedule.fetch (x : D.EmitRow) : CentreMachine sel d (D.tag x) bank q :=
  D.centre x.val x.property

/-- The receiver below is a proof view for reusing the verified R49
arithmetic and ledger, not an operation of the byte program. -/
def Schedule.proofCentre (t : Center S c) : CentreMachine sel d t bank q :=
  D.proofRow_key t ▸ D.fetch (D.proofRow t)

private theorem transport_from_same_row (x y : D.EmitRow) (e : x=y) (val : D.tag x=D.tag y) :
    (val ▸ D.fetch x : CentreMachine sel d (D.tag y) bank q)=D.fetch y := by
  subst y
  rfl

theorem Schedule.proofCentre_on_emission (x : D.EmitRow) :
    D.proofCentre (D.tag x)=D.fetch x := by
  exact transport_from_same_row D _ x (D.tag_inj (D.proofRow_key (D.tag x))) (D.proofRow_key (D.tag x))

def Schedule.extra : ℕ := bitsValue D.stock.margin.val

def Schedule.proofView : ActiveMachine sel d bank q where
  extraPrecision := D.extra
  enough := D.marginExact.symm.le
  centres := D.centresView
  centreUnique := D.centres_unique
  centreComplete := D.centres_complete
  tape := D.proofCentre

abbrev Schedule.high (hp : 0<c.prec) : Frame f (c.prec+D.extra) :=
  bank (c.prec+D.extra) (Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _))

def Schedule.highRun (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) : Meter (Block (D.high hp) ell) :=
  sumRaw (D.high hp).hp (fun x hx=>(D.centre x hx).runCentre hq hv hf (D.high hp) D.extra
      (child (centreFor D.roster x hx))) D.stock.rows (fun _ hx=>hx)

theorem Schedule.high_run_is_the_exact_proof_fold
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) :
    D.highRun hq hp hv hf child=D.proofView.highRun hq hp hv hf child := by
  apply raw_fold_meter_is_in_the_emission_order _ _
    (fun x hx=>D.tag ⟨x,hx⟩) (fun t=>(D.proofCentre t).runCentre hq hv hf (D.high hp) D.extra (child t))
    D.stock.rows (fun _ hx=>hx)
  intro x hx
  change (D.fetch ⟨x,hx⟩).runCentre _ _ _ _ _ _ =
    (D.proofCentre (D.tag ⟨x,hx⟩)).runCentre _ _ _ _ _ _
  rw [D.proofCentre_on_emission]
  rfl

def Schedule.eval (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) : Meter (Block (bank c.prec hp) ell) :=
  let ran := D.highRun hq hp hv hf child
  let low := bank c.prec hp
  let strip := stripUVLoop (((D.high hp).natDegree hf).trans (low.natDegree hf).symm) ran.result
  checkedWord (zeroM low.hp) ⟨strip.result,ran.steps+strip.steps+4⟩

theorem Schedule.exact_sweep_matches_its_own_proof_view
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) :
    D.eval hq hp hv hf child=D.proofView.eval hq hp hv hf child := by
  unfold Schedule.eval ActiveMachine.eval ActiveMachine.finish
  dsimp only
  rw [D.high_run_is_the_exact_proof_fold]
end

#print axioms raw_fold_meter_is_in_the_emission_order
#print axioms Schedule.centres_in_order
#print axioms Schedule.proofCentre_on_emission
#print axioms Schedule.exact_sweep_matches_its_own_proof_view
end J6R68ActiveInputs.Sweep
