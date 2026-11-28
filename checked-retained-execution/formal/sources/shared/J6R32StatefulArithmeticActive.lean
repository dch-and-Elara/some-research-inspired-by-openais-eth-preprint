import J6R32StatefulArithmeticSite

/-! The R24 local active interpreter with a single live state. This is
the R24 centre roster, probe indices, mode lists, group order and existing
UV/jet kernels; only the child effect changes. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial
open Polynomial A1R10 A1R12 AOracleMachineTime J6R22Active J6R19Retained
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R23ScheduleWeight

variable {f : ℤ[X]} {ell s : ℕ} {σ : Type*}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f}
local notation "a" => (Shape.levelBits S (Call.depth c))
local notation "u" => (Shape.levelWidth S (Call.depth c))

abbrev CentreChildS (σ : Type*) (bank : Bank f) (d : Ready S (sourceDelta s) c)
    (t : Center S c) :=
  Probe S c→NativeMenu (N sel) c t→Fin 64→SM σ (Block (bank (registerPrecision S c t) (register_positive d t)) ell)

abbrev ActiveChildS (σ : Type*) (bank : Bank f) (d : Ready S (sourceDelta s) c) :=
  ∀ t : Center S c,CentreChildS (sel:=sel) σ bank d t

variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
local notation "pₜ" => (registerPrecision S c t)
local notation "kₜ" => (order (Call.edges c) u (Subtype.val t))

def centreS {q : ℕ} (D : CentreDesc sel d t bank) (hv : 0<ell)
    (hf : f.Monic) (high : Frame f q) (B : ℕ)
    (child : CentreChildS (sel:=sel) σ bank d t) : SM σ (Block high ell) :=
  let F := bank pₜ (register_positive d t)
  -- siteS uses only the roster, masks and modes of this record.
  let J := D.site hv (fun _ _ _=>zeroM F.hp)
  finish (siteS J a t.val child) (fun jet=>
    padCost (sumM high.hp (D.term hv hf high B jet) (List.range kₜ)) (tapeFee F.words.length ell pₜ kₜ+4))

set_option maxHeartbeats 2500000 in
theorem centre_sound {q : ℕ} {I : σ→Prop} (D : CentreDesc sel d t bank)
    (hv : 0<ell) (hf : f.Monic) (high : Frame f q) (B : ℕ)
    (child : CentreChildS (sel:=sel) σ bank d t)
    (ref : CentreChild (sel:=sel) (d:=d) (t:=t) bank)
    (exactChild : ∀ z m g,Sound I (child z m g) (ref z m g)) :
    Sound I (centreS D hv hf high B child) (D.centre hv hf high B ref) := by
  let F := bank pₜ (register_positive d t)
  have h := site_sound (D.site hv ref) a t.val child exactChild
  have z := h.finish (fun jet=>
    padCost (sumM high.hp (D.term hv hf high B jet) (List.range kₜ)) (tapeFee F.words.length ell pₜ kₜ+4))
  simpa only [merge,padCost,CentreDesc.centre,Nat.add_assoc] using z

def highS (D : ActiveDesc sel d bank) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChildS (sel:=sel) σ bank d) : SM σ (Block (D.high hp) ell) :=
  sumWords (D.high hp).hp (fun t=>centreS (D.tape t) hv hf (D.high hp) D.extraPrecision (child t)) D.centres

def finishS (D : ActiveDesc sel d bank) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChildS (sel:=sel) σ bank d) : SM σ (Option (Block (bank c.prec hp) ell)) :=
  finish (highS D hp hv hf child) (fun v=>
    padCost (stripUVLoop (((D.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm) v) 4)

def activeS (D : ActiveDesc sel d bank) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChildS (sel:=sel) σ bank d) : SM σ (Block (bank c.prec hp) ell) :=
  stripCheck (zeroM (bank c.prec hp).hp) (finishS D hp hv hf child)

set_option maxHeartbeats 2500000 in
theorem active_sound {I : σ→Prop} (D : ActiveDesc sel d bank) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChildS (sel:=sel) σ bank d) (ref : ActiveChild (sel:=sel) (d:=d) bank)
    (exactChild : ∀ t z m g,Sound I (child t z m g) (ref t z m g)) :
    Sound I (activeS D hp hv hf child) (D.eval hp hv hf ref) := by
  have x : Sound I (highS D hp hv hf child) (D.highRun hp hv hf ref) :=
    sumWords_sound (D.high hp).hp _ _ _ (fun t _=>
      centre_sound (D.tape t) hv hf (D.high hp) D.extraPrecision (child t) (ref t) (exactChild t))
  have y := x.finish (fun v=>
    padCost (stripUVLoop (((D.high hp).natDegree hf).trans ((bank c.prec hp).natDegree hf).symm) v) 4)
  have z : Sound I (finishS D hp hv hf child) (D.finish hp hv hf ref) := by
    simpa only [finishS,merge,ActiveDesc.finish,padCost,Nat.add_assoc] using y
  exact strip_sound z

#print axioms centre_sound
#print axioms active_sound
end J6R32StatefulArithmetic
