import J6R24MeteredRecursionCentre

/-! Ordered centre pass and final checked strip. A jet is local to its
centre loop. Across centres one keeps only a high accumulator, so an
external directory of jet tapes or a free jet lookup is not used. -/
namespace J6R24MeteredRecursion
open scoped Polynomial
open Polynomial A1R10 A1R12 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R22Active J6R23ScheduleWeight J6R19Retained HermiteLoss

variable {f : ℤ[X]} {ell s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
local notation "a" => (Shape.levelBits S (Call.depth c))
local notation "u" => (Shape.levelWidth S (Call.depth c))

structure ActiveDesc (bank : Bank f) where
  extraPrecision : ℕ
  enough : commonLoss a c.edges u≤extraPrecision
  centres : List (Center (printedParams (f:=f) (ell:=ell) s) c)
  centreUnique : centres.Nodup
  centreComplete : ∀ t,t∈centres
  tape : ∀ t,CentreDesc sel d t bank

variable {sel d} {bank : Bank f}
variable (D : ActiveDesc sel d bank)
variable (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)

abbrev ActiveChild (bank : Bank f) := ∀ t : Center S c,
  CentreChild (sel:=sel) (d:=d) (t:=t) bank

abbrev ActiveDesc.high := bank (c.prec+D.extraPrecision) (Nat.lt_of_lt_of_le hp (Nat.le_add_right ..))

def ActiveDesc.highRun (child : ActiveChild (sel:=sel) (d:=d) bank) :
    Meter (Block (D.high hp) ell) :=
  sumM (D.high hp).hp (fun t=>(D.tape t).centre hv hf (D.high hp) D.extraPrecision (child t)) D.centres

def ActiveDesc.finish (child : ActiveChild (sel:=sel) (d:=d) bank) :
    Meter (Option (Block (bank c.prec hp) ell)) :=
  let v := D.highRun hp hv hf child
  let rc := stripUVLoop (((D.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm) v.result
  ⟨rc.result,v.steps+rc.steps+4⟩

/-- Sticky local failure is checked before choosing a word. On a legal
run the fallback is never reached, proved by the source strip theorem. -/
def checkedWord {A : Type*} (z : Meter A) (v : Meter (Option A)) : Meter A :=
  match v.result with
  | some x => ⟨x,v.steps+2⟩
  | none => ⟨z.result,v.steps+z.steps+2⟩

theorem checked_delta {A : Type*} {x y : Meter (Option A)} {j : ℕ}
    (z : Meter A) (h : Delta x y j) : Delta (checkedWord z x) (checkedWord z y) j := by
  rcases h with ⟨hValue,hFee⟩
  cases hy : y.result with
  | none =>
    have hx : x.result=none := hValue.trans hy
    refine ⟨?_,?_⟩
    · simp only [checkedWord,hx,hy]
    · simp only [checkedWord,hx,hy,hFee]
      omega
  | some aval =>
    have hx : x.result=some aval := hValue.trans hy
    refine ⟨?_,?_⟩
    · simp only [checkedWord,hx,hy]
    · simp only [checkedWord,hx,hy,hFee]
      omega

def ActiveDesc.eval (child : ActiveChild (sel:=sel) (d:=d) bank) :
    Meter (Block (bank c.prec hp) ell) :=
  checkedWord (zeroM (bank c.prec hp).hp) (D.finish hp hv hf child)

def ActiveDesc.children (child : ActiveChild (sel:=sel) (d:=d) bank) : ℕ :=
  (D.centres.map (fun t=>((D.tape t).site hv (child t)).childBill)).sum

theorem ActiveDesc.one_visit (child : ActiveChild (sel:=sel) (d:=d) bank) :
    Delta (D.eval hp hv hf child) (D.eval hp hv hf (fun t z β g=>bare (child t z β g)))
      (D.children hv child) := by
  have h0 := sum_delta (D.high hp).hp
    (fun t=>(D.tape t).centre hv hf (D.high hp) D.extraPrecision (child t))
    (fun t=>(D.tape t).centre hv hf (D.high hp) D.extraPrecision (fun z β g=>bare (child t z β g)))
    (fun t=>((D.tape t).site hv (child t)).childBill) D.centres
    (fun t _=>(D.tape t).once_delta hv hf (D.high hp) D.extraPrecision (child t))
  have hrun : Delta (D.highRun hp hv hf child)
      (D.highRun hp hv hf (fun t z β g=>bare (child t z β g))) (D.children hv child) := h0
  apply checked_delta
  refine ⟨?_,?_⟩
  · simp only [ActiveDesc.finish,hrun.value]
  · simp only [ActiveDesc.finish,hrun.value,hrun.fee]
    omega

#print axioms ActiveDesc.one_visit
end J6R24MeteredRecursion


