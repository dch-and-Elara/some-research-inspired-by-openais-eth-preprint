import J6R49DFSActive
import J6R24MeteredRecursionTight
import J6R24MeteredRecursionActiveValue

/-! Select precisely the sufficient common Hermite scale in the streamed
active interpreter. This is a representation choice; candidate
selection, raw arithmetic and full-run cost are separate obligations. -/
namespace J6R49LiveBits
open scoped Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost J6R21Ancestor
open J6R22Active J6R24MeteredRecursion J6R49DFS HermiteLoss

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {f : ℤ[X]} {ell s C : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {bank : Bank f} {q : ℕ}

def canonicalActive (D : ActiveMachine sel d bank q) : ActiveMachine sel d bank q :=
  { D with extraPrecision := commonLoss (Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth) c.edges (Shape.levelWidth (printedParams (f:=f) (ell:=ell) s) c.depth), enough := le_rfl }

theorem canonical_common_field_budget (cfg : RootBounds s C f) (hr : Stable s C r)
    (walk : NativeReach (Plan sel) r c) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    (D : ActiveMachine sel d bank q) :
    let lam := Nat.clog 2 s
    c.prec+(canonicalActive D).extraPrecision≤
      precisionSize s C+c.edges*(24*2^lam+4*(lam+1)) := by
  have hp := every_call_precision_cap cfg sel r walk hr hzero hroot
  obtain ⟨hu,huM⟩ := (J6R12Integral.printedGuards cfg sel r hr).taper _ walk d.active
  have ha : Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth≤Nat.clog 2 s := bits_le_lam _ _
  exact Nat.add_le_add hp (simple_common_scale_cap ha hu huM)

theorem canonical_active_source_decoded [DecidableEq (Envelope (N sel) (Childs sel) r)]
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (cfg : RootBounds s C f) (hr : Stable s C r) (walk : NativeReach (Plan sel) r c)
    (D : ActiveMachine sel d bank q) (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell)
    (hf : f.Monic) (child : ActiveChild (sel:=sel) (d:=d) bank)
    (hChild : ∀ t z β g,(bank (registerPrecision (printedParams (f:=f) (ell:=ell) s) c t) (register_positive d t)).decode
      (child t z β g).result=(J6R12Blueprint.sourceBlueprint sel r hf).program.run
        ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩)) :
    (bank c.prec hp).decode ((canonicalActive D).eval hq hp hv hf child).result =
      (J6R12Blueprint.sourceBlueprint sel r hf).program.run c := by
  rw [active_stream_value (canonicalActive D) hq hp hv hf child]
  obtain ⟨x,_,hval,hdec⟩ := actual_active_decoded cfg sel r hf walk d hr
    (canonicalActive D).prior hp hv child hChild
  rw [hval, hdec]

#print axioms canonical_common_field_budget
#print axioms canonical_active_source_decoded
end J6R49LiveBits



