
import A2R45LiteralAdmission
import J6R14ZeroModeRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 1800
set_option linter.unusedSectionVars false

/-! Actual agenda address for the zero mode at an existing probe index.
The dependent site alphabet is the original one. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R12Blueprint J6R11Blueprint J6R11Repack J1PPrinted

noncomputable section
variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable (sel : Selector S Δ) {c : Call (PhysicalHost f ell)}
variable (d : Ready S Δ c) (t : Center S c)

def stockZeroMode : NativeMenu (shape S Δ sel) c t := by
  let A := (shape S Δ sel).Mode c t
  letI : Fintype A := (shape S Δ sel).finiteMode c t
  letI : DecidableEq A := (shape S Δ sel).decideMode c t
  let p := registerPrecision S c t
  let ww : A→ℕ := (shape S Δ sel).weight c t
  have hp : 0<p := register_positive d t
  have hw : ∀ m : A,0<ww m := weightAt_pos S Δ sel c t
  change {β : A→₀ℕ // β ∈ J6RecursiveMenu.menu p ww}
  refine ⟨0,?_⟩
  rw [J6RecursiveMenu.exact_printed_menu p ww hw]
  simpa [J6RecursiveMenu.weighted] using hp

def stockAddress (z : Probe S c) (g : Fin 64) : NativeAddress (shape S Δ sel) c :=
  ⟨t,z,stockZeroMode sel d t,g⟩

theorem stockAddress_tuple_zero (z : Probe S c) (g : Fin 64) :
    siteTuple sel d (stockAddress sel d t z g)=0 := by
  unfold siteTuple
  change Finsupp.embDomain (Equiv.cast (modeAt_eq S Δ sel d t)).toEmbedding
    (0 : modeAt S Δ sel c t→₀ℕ)=0
  exact Finsupp.embDomain_zero _

theorem stock_child_is_packet (z : Probe S c) (g : Fin 64) :
    (nativePlan (shape S Δ sel) (children S Δ sel)).child c
      ⟨stockAddress sel d t z g,d.active⟩ =
    let H := packetOfSite sel d t z 0 g
    ⟨H,c.depth+1,H.edgeCount,registerPrecision S c t⟩ := by
  rw [child_exact sel d,stockAddress_tuple_zero]
  rfl

#print axioms stockZeroMode
#print axioms stockAddress_tuple_zero
#print axioms stock_child_is_packet
end
end A2R45Literal
