import J6R53PublicMountFreshReadout
import J6R53PublicMountCharge

/-! Same-meter wrapper for the actual fresh submitted CNF:
the final word and every printed mount bill belong to one execution. -/
namespace J6R53PublicMount
open scoped Classical Polynomial BigOperators
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6OrientedHostEval J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R33OriginalJ6 J6R28GeneratedRootFrame J6R22RootReadout
open J6R34OfficialGateway J6R34RootAtlas J6R27OriginalGate J6R14ZeroMode J6R36SharedGateway
open J6R51Ingress J6R52FreshShape J7R9Compiler J7R9Subdivision J7R10Plant
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 6800000
set_option linter.unusedSectionVars false
set_option Elab.async false
attribute [local irreducible] J6R51Ingress.freshPlant J6R51Ingress.guardedInOrder
attribute [local irreducible] runMountedCount
noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (C : CNF V) (order : DeclaredOrder V)
local notation "graphF" => (guardedInOrder C order.roster)
local notation "plantF" => (freshPlant graphF (guardRoster order))
local notation "mF" => (nWires graphF)
local notation "nF" => (nSubdiv graphF)
local notation "vF" => (OrderedOld graphF)
variable {f : ℤ[X]} {base native ell q rr cc dd edgew tc tj key prec tw bw rate pad : ℕ}
variable (G : RootShape f (nWires (guardedInOrder C order.roster))
  (printedHalf (nWires (guardedInOrder C order.roster))) base native
  (printedRankWidth (nWires (guardedInOrder C order.roster)))
  (freshPlant (guardedInOrder C order.roster) (guardRoster order))
  (constantRootWord (nWires (guardedInOrder C order.roster))))
variable (hf : f.Monic)
variable (frame : Frame f (J6SourcePrecision.printed (nWires (guardedInOrder C order.roster)) base))
variable (hv : 0<ell)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (groups : MountedFamily (V:=OrderedOld (guardedInOrder C order.roster)) (f:=f)
  (m:=nWires (guardedInOrder C order.roster)) (n:=nSubdiv (guardedInOrder C order.roster))
  (base:=base) (native:=native) (T:=freshPlant (guardedInOrder C order.roster) (guardRoster order))
  G ell q rr cc dd edgew tc tj key prec tw bw rate pad)


theorem fresh_count_and_every_mount_share_the_meter :
    let out := freshCountMeter C order G hf frame hv groups
    bitsValue out.result.val=PinnedCNF.modelCount C ∧
      (∑ i : J6Recovery.Addr mF, ∑ j : Fin (literalDegree mF native+1),
        ∑ g : Fin 64, groupCharge G i j (groups i j g)) ≤ out.steps := by
  let centre : J6Recovery.Addr mF := ⟨0,Nat.zero_lt_succ _⟩
  let probe : Fin (literalDegree mF native+1) := ⟨0,Nat.zero_lt_succ _⟩
  have basePositive : 0<base := (groups centre probe 0).job.basePositive
  have value := fresh_mounted_public_count_word (f:=f) (base:=base) (native:=native)
    (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd) (edgew:=edgew) (tc:=tc) (tj:=tj)
    (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) (rate:=rate) (pad:=pad)
    C order G hf frame hv groups basePositive
  have payment := run_mounted_count_pays_every_printed_mount (V:=vF) (f:=f) (m:=mF) (n:=nF)
    (base:=base) (native:=native) (T:=plantF) (ell:=ell) (q:=q) (rr:=rr) (cc:=cc) (dd:=dd)
    (edgew:=edgew) (tc:=tc) (tj:=tj) (key:=key) (prec:=prec) (tw:=tw) (bw:=bw)
    (rate:=rate) (pad:=pad) G hf frame hv groups
  exact ⟨value,payment⟩

#print axioms fresh_count_and_every_mount_share_the_meter
end
end J6R53PublicMount
