import J6R57PublicRequestAdmit

/-! A resident row can now be submitted without an external address
or a supplied hit. The paid prescribed sample read precedes the
native gate. Its result is the queue's actual live original atlas. -/
namespace J6R57PublicRequest
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R33StatefulArithmeticPage
open J6R31RootResidentTables J6R30ProducedGateRegistry J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 4200
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (C : Compiled G ell q rr cc dd prec kp bw)
variable (S : InstalledRequestInputs W C) (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))

def submitResidentRow (row : Entry C.mark m native tc tj tw) :
    Meter (Option (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) × Bool)) :=
  let request := S.requests.probes.read row.coord.1.2
  let run := admitRequest C S pad B row.wire request.result.val
  ⟨run.result,request.steps+run.steps+3⟩

theorem generated_public_row_returns_live_original_bank
    (sync : B.synced) (reserved : ∀ row∈B.headers,row.id.bits.take kp≠C.mark.bits)
    (row : Entry C.mark m native tc tj tw) (stored : row∈S.requests.rows) :
    let X := (entrySource (W:=W) C row).result
    let request := S.requests.probes.read row.coord.1.2
    let run := submitResidentRow C S pad B row
    ∃ bank,run.result=some (bank,true) ∧ IsLive (X.seed pad) bank ∧
      run.steps=request.steps+(admitRequest C S pad B row.wire request.result.val).steps+3 := by
  rw [S.requests.ordered,(catalogue_exact_order_and_bill W C.mark).1] at stored
  obtain ⟨x,_,equal⟩ := List.mem_map.mp stored
  subst row
  let r := (emitAt W C.mark x).result
  let Q := S.requests.probes.read x.1.2
  let X := (entrySource (W:=W) C r).result
  let out := (X.seed pad).install B
  obtain ⟨_,t,j,g,_,_⟩ := actual_entry_wires W C.mark x
  have exact := a_true_address_mounts_the_original_native_seed C S pad B sync reserved r.wire x t j g
      Q.result.val (S.requests.probes.consistent x.1.2)
  have legal : (submitResidentRow C S pad B r).result=some out.result := exact.1
  have ok : out.result.2=true := exact.2.1
  have Live : IsLive (X.seed pad) out.result.1 :=
    (actual_public_live_from_common_bank W C x.1.1 x.1.2 x.2 pad B sync reserved).2
  have pair : out.result=(out.result.1,true) := Prod.ext rfl ok
  exact ⟨out.result.1,legal.trans (congrArg some pair),Live,rfl⟩

#print axioms submitResidentRow
#print axioms generated_public_row_returns_live_original_bank
end
end J6R57PublicRequest
