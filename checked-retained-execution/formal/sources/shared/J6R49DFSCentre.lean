import J6R49DFSCentreBase

/-! Compare each verified streamed centre with the old value semantics.
Only the proof inputs mention a complete legal mode list. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R9Recursive J6R24MeteredRecursion J1PPrinted

set_option autoImplicit false
set_option maxHeartbeats 7600000
set_option maxRecDepth 2600

variable {f : ℤ[X]} {ell s q highPrec : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c} {bank : Bank f}

theorem centre_jet_stream_value (J : CentreMachine sel d t bank q) (hq : 0<q) (hv : 0<ell) (hf : f.Monic)
    (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank)
    (modes : List (NativeMenu (N sel) c t)) (nd : modes.Nodup) (complete : ∀ β,β∈modes) :
    (J.centreJet hq hv child).result=
      (((J.priorCentre modes nd complete).site hv child).run
        ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth) t.val).result := by
  exact same_center_jet_words hf J.low J.tape.result hq hv
    (active_order_pos ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)
      c.edges ((printedParams (f:=f) (ell:=ell) s).levelWidth c.depth) t.val t.property)
    J.masks J.roster.rows child modes nd complete

theorem centre_stream_value (J : CentreMachine sel d t bank q)
    (hq : 0<q) (hv : 0<ell) (hf : f.Monic) (high : Frame f highPrec) (B : ℕ)
    (child : CentreChild (sel:=sel) (d:=d) (t:=t) bank)
    (modes : List (NativeMenu (N sel) c t)) (nd : modes.Nodup) (complete : ∀ β,β∈modes) :
    (J.runCentre hq hv hf high B child).result=
      ((J.priorCentre modes nd complete).centre hv hf high B child).result := by
  unfold CentreMachine.runCentre CentreDesc.centre
  dsimp only
  rw [centre_jet_stream_value J hq hv hf child modes nd complete]
  rfl

#print axioms centre_jet_stream_value
#print axioms centre_stream_value
end J6R49DFS
