import J6R16ModeCostEnvelope
import J6R19RetainedCost

/-! Frame promotion alone, not the arithmetic of the ancestor entry
evaluator. At a printed active site both sizes are bounded by the
actual receiving register, since the true creation tag is stable. -/
namespace J6R20Ancestor
open scoped Polynomial
open J6R19Retained J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable
open J6R11Blueprint J6R11Repack J6R12Blueprint J6R16ModeCost

def promotionFixed (e ell oldWidth newWidth : ℕ) : ℕ :=
  6*oldWidth+4*newWidth+ell*(16*e+16)+29

theorem promoteFee_of_le (e ell p q oldWidth newWidth : ℕ) (h : p≤q) :
    promoteFee e ell p q oldWidth newWidth≤22*ell*e*q+promotionFixed e ell oldWidth newWidth := by
  calc
    _≤promoteFee e ell q q oldWidth newWidth := by
      rw [promoteFee_closed_form,promoteFee_closed_form]
      gcongr
    _=_ := by rw [promoteFee_closed_form,promotionFixed]; ring

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))

include cfg in
theorem reachable_retained_promote_budget {r c : Call (PhysicalHost f ell)}
    (walk : NativeReach (Plan sel) r c) (root : Stable s C r) (d0 : r.depth=0)
    (p0 : r.prec≤C*s) (live : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c)
    (v : c.host.Row ⊕ c.host.Col) (oldWidth newWidth : ℕ) :
    let lam := Nat.clog 2 s
    let u := stepU lam c.depth
    let a := stepA lam c.depth
    let D := 2^(a-padicValInt 2 t.val)
    let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
    let e := f.natDegree
    promoteFee e ell (c.host.file v).created p oldWidth newWidth*u ≤
      22*ell*e*(siteConstant C*c.edges*D)+promotionFixed e ell oldWidth newWidth*u := by
  let lam := Nat.clog 2 s
  let u := stepU lam c.depth
  let a := stepA lam c.depth
  let D := (2:ℕ)^(a-padicValInt 2 t.val)
  let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
  let e := f.natDegree
  let old := (c.host.file v).created
  have hS := (stable_reachable cfg sel walk root).tags v
  have hP : c.prec≤p := by
    change c.prec≤childPrecision c.prec a c.edges u t.val
    exact (child_monotone c.prec a c.edges u t.val (Nat.zero_lt_of_lt live)).le
  have hReg : p*u≤siteConstant C*c.edges*D := (register_envelope cfg sel walk root d0 p0 live t).2.2.2
  have hOld : old≤p := hS.trans hP
  change promoteFee e ell old p oldWidth newWidth*u≤_
  calc
    _≤(22*ell*e*p+promotionFixed e ell oldWidth newWidth)*u :=
      Nat.mul_le_mul_right _ (promoteFee_of_le e ell old p oldWidth newWidth hOld)
    _=22*ell*e*(p*u)+promotionFixed e ell oldWidth newWidth*u := by ring
    _≤_ := Nat.add_le_add_right (Nat.mul_le_mul_left _ hReg) _

#print axioms promoteFee_of_le
#print axioms reachable_retained_promote_budget
end J6R20Ancestor

