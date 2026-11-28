import J6R54PublicFamilyMount
import J6R53PublicMountGateway

/-! Shared compiled data are captured once in the query program. The
original legal-byte check controls emission of the head and group
addresses; offline setup is charged once, outside the whole program. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R34RootAtlas J6R53PublicMount J6R53WordIngress J6R27OriginalGate
open J6R14ZeroMode J6R33OriginalJ6 J6R32RootGeneratedRegistryInputs
open J6R36SharedGateway J6R22Active
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15500000
set_option maxRecDepth 3300
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew rate pad : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (R : PublicJobs W C rate pad)
variable (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)

def sourcePublicQuery : SlotProgram (ell:=ell) (F:=C.frame) G :=
  fun i j raw =>
    let expected := A.read j
    let test := eqRawBits raw expected.result.val
    if test.result then
      let M := cachedPublicSlot W C R i j
      ⟨M.result,expected.steps+test.steps+M.steps+4⟩
    else
      let reject := zeroM (ell:=ell) (SiteFrame G ell C.frame i).hp
      ⟨reject.result,expected.steps+test.steps+reject.steps+4⟩

variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1))
variable (raw : List Bool)

def locationFee : ℕ :=
  (prepareHead W i j).steps+(∑ g : Fin 64,(ordinalFee 6 g.val+11))+4

theorem actual_public_query_bill
    (legal : raw=List.ofFn ((rootPreset G ell).word j)) :
    sourcePublicQuery W C R A i j raw =
      addIngressCharge (paidMountedQuery G C.hf C.frame C.positive
        (plainFamily W C R) A i j raw) (locationFee W i j) := by
  have same : raw=(A.read j).result.val := legal.trans (A.consistent j).symm
  have pass := (eq_raw_bits_exact raw (A.read j).result.val).1.mpr same
  have H := cached_slot_exact_plain_and_fee W C R i j
  rw [legal_query_is_actual_mount_meter G C.hf C.frame C.positive (plainFamily W C R) A i j raw legal]
  unfold sourcePublicQuery addIngressCharge
  dsimp only
  rw [if_pos pass,H.1,H.2]
  let M := mountedSlot G C.hf C.frame i j C.positive (plainFamily W C R i j)
  let x := (A.read j).steps
  let y := (eqRawBits raw (A.read j).result.val).steps
  let Hfee := (prepareHead W i j).steps
  let p := ∑ g : Fin 64,(ordinalFee 6 g.val+11)
  change (⟨M.result,x+y+(Hfee+(M.steps+p)+4)+4⟩ :
    Meter (Block (SiteFrame G ell C.frame i) ell)) =
    ⟨M.result,(Hfee+p+4)+(x+y+M.steps+4)⟩
  have eq : x+y+(Hfee+(M.steps+p)+4)+4=(Hfee+p+4)+(x+y+M.steps+4) := by omega
  rw [eq]

theorem actual_public_query_same_original
    (legal : raw=List.ofFn ((rootPreset G ell).word j)) :
    (sourcePublicQuery W C R A i j raw).result =
      (mountedOracle G C.hf C.frame C.positive (plainFamily W C R)).reply i j raw := by
  rw [actual_public_query_bill W C R A i j raw legal]
  exact legal_mount_matches_original_oracle G C.hf C.frame C.positive
    (plainFamily W C R) A i j raw legal

theorem rejected_public_query_skips_actual_words
    (bad : raw≠List.ofFn ((rootPreset G ell).word j)) :
    sourcePublicQuery W C R A i j raw =
      paidMountedQuery G C.hf C.frame C.positive (plainFamily W C R) A i j raw := by
  have wrong : raw≠(A.read j).result.val := fun h=>bad (h.trans (A.consistent j))
  have no : ¬(eqRawBits raw (A.read j).result.val).result :=
    fun h=>wrong ((eq_raw_bits_exact raw (A.read j).result.val).1.mp h)
  unfold sourcePublicQuery paidMountedQuery
  dsimp only
  simp only [if_neg no]

variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable (jobs : PublicJobs W (prepareShared I).result rate pad)

def preparePublicProgram :
    Meter (SlotProgram (ell:=ell) (F:=(prepareShared I).result.frame) G) :=
  let C := prepareShared I
  let Probe := buildRootBitBank G ell
  ⟨sourcePublicQuery W C.result jobs Probe.result,C.steps+Probe.steps+6⟩

theorem actual_public_program_init :
    let S := preparePublicProgram W I jobs
    S.result=sourcePublicQuery W (prepareShared I).result jobs (buildRootBitBank G ell).result ∧
      S.steps=(prepareShared I).steps+(buildRootBitBank G ell).steps+6 :=
  ⟨rfl,rfl⟩

#print axioms actual_public_query_bill
#print axioms actual_public_query_same_original
#print axioms rejected_public_query_skips_actual_words
#print axioms actual_public_program_init
end
end J6R54PublicFamily

