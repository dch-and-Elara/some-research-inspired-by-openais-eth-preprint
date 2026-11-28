import J6R57PublicRequestBind
import J6R35GatewayPreparationSeed

/-! The selector consumes the one paid resident-port/field/probe cache
obtained from the *same* common source. The compiler equality holds
for every catalogue entry and is not a supplied per-request condition. -/
namespace J6R57PublicRequest
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3900
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable (C : Compiled G ell q rr cc dd prec kp bw)

def buildCommonRoot : Meter (ActualRootPreparation G ell q) :=
  prepareSharedRoot G C.literal ell ⟨C.frame,0⟩
    (Nat.zero_lt_one.trans (copy_width_above_one (by rw [←C.copiesOK]; exact val_lt C.regs.copies)))
    C.regs.copies C.regs.pre

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem one_root_cache_for_every_entry (r : Entry C.mark m native tc tj tw) :
    buildCommonRoot C=rootPreparationFor (entrySource (W:=W) C r).result := by
  rfl

structure InstalledRequestInputs
    (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw) where
  root : ActualRootPreparation G ell q
  exactRoot : root=(buildCommonRoot C).result
  requests : PreparedRequests W C
  sameProbes : requests.probes=root.probes

def buildRequestInputs (W : Widths m native tc tj tw edgew) : Meter (InstalledRequestInputs W C) :=
  let R := buildCommonRoot C
  let D := emitCatalogue W C.mark
  ⟨⟨R.result,rfl,⟨R.result.probes,D.result,rfl⟩,rfl⟩,R.steps+D.steps+5⟩

theorem single_actual_input_cache (W : Widths m native tc tj tw edgew) :
    let S := buildRequestInputs C W
    S.result.requests.probes=(buildRootBitBank G ell).result ∧
      S.result.requests.rows=(emitCatalogue W C.mark).result ∧
      S.steps=(buildCommonRoot C).steps+(emitCatalogue W C.mark).steps+5 :=
  ⟨rfl,rfl,rfl⟩

def compileRequestInputs (W : Widths m native tc tj tw edgew) (I : SharedInputs G ell q rr cc dd prec kp bw) :
    Meter (InstalledRequestInputs W (prepareShared I).result) :=
  let C := prepareShared I
  let D := buildRequestInputs C.result W
  ⟨D.result,C.steps+D.steps+3⟩

theorem compiled_request_cache_exact_fee
    (W : Widths m native tc tj tw edgew) (I : SharedInputs G ell q rr cc dd prec kp bw) :
    let C := prepareShared I
    let S := compileRequestInputs W I
    S.steps=C.steps+(buildCommonRoot C.result).steps+(emitCatalogue W C.result.mark).steps+8 := by
  dsimp only [compileRequestInputs,buildRequestInputs]
  omega

#print axioms one_root_cache_for_every_entry
#print axioms single_actual_input_cache
#print axioms compiled_request_cache_exact_fee
end
end J6R57PublicRequest
