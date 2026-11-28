import J6R68RateJointRootWordsInput
import J6R49SourceLayoutOrder
import J6R16ModeCostSite

/-! Native first-template copy does not require an assumed callback cap.
An explicit radius for its real word widths gives a linear census
charge plus the real product of modulus precision and degree. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R26DescriptorTree J6R33GeneratedChildSite J6R34RootAtlas J6R49SourceLayout
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6ActiveSchedule
open J6R10Repack J6R30ProducedGateRegistry J6R16ModeCost J6R32ChildResidentTransfer

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4300
set_option maxHeartbeats 16000000
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => ((SP).levelBits v.parent.depth)
local notation "P" => (registerPrecision SP v.parent v.centerAt)
local notation "D" => (ticketReady T v)
local notation "I₀" => (centerIndex (ticketReady T v) v.centerAt)

theorem true_first_edge_and_mask_census (I : OccurrenceInput T v key prec tw bw page) :
    I.geometry.edges.length=v.parent.edges ∧
      I.physical.result.raw.masks.length=(2^(6*A)*2^(6*A))*(packing sel D).copies := by
  letI : Fintype v.parent.host.Edge := v.parent.host.finiteEdge
  have h := full_roster_length I.geometry.edges I.geometry.edgesUnique I.geometry.edgesAll
  have k : Fintype.card v.parent.host.Edge=v.parent.edges := (D).edgeCount
  refine ⟨h.trans (Nat.card_eq_fintype_card.trans k),?_⟩
  rw [I.geometry.masks,List.length_map,(child_pages_complete A (packing sel D).copies).2.2]

structure ActualFirstWidths (I : OccurrenceInput T v key prec tw bw page) (K : ℕ) : Prop where
  keyFit : key≤K
  centreFit : I.tc≤K
  probeFit : I.tz≤K
  modeFit : I.tm≤K
  depthFit : I.dep≤K
  rankFit : I.q≤K
  receiveFit : prec≤K
  timeFit : tw≤K
  codeFit : bw≤K
  logFit : Nat.clog 2 s≤K
  modulusFit : P≤K

theorem exact_first_copy_tariff_bounded_by_true_widths
    (I : OccurrenceInput T v key prec tw bw page) (K : ℕ) (X : ActualFirstWidths I K) :
    firstReplayTariff I (13*key+4)+4 ≤
      (128*(K+1))*(1+K+v.parent.edges+I.physical.result.raw.masks.length+I.geometry.modes.length) := by
  let b := 128*(K+1)
  let lam := Nat.clog 2 s
  let a := A
  let Q := I.q
  let ne := v.parent.edges
  let nm := I.physical.result.raw.masks.length
  let ns := I.geometry.modes.length
  have xA : a≤K := (bits_le_lam _ _).trans X.logFit
  have xI : (I₀).val≤K := (I₀).isLt.le.trans xA
  have pfit := X.modulusFit
  have qfit := X.rankFit
  have ekey := X.keyFit
  have ec := X.centreFit
  have ez := X.probeFit
  have em := X.modeFit
  have ed := X.depthFit
  have ep := X.receiveFit
  have et := X.timeFit
  have eb := X.codeFit
  have el : lam≤K := X.logFit
  have bs : (3*(a+((Q-a)+13*a))+51)*ne≤b*ne :=
    Nat.mul_le_mul_right ne (by dsimp only [b]; omega)
  have bm : (39*a+3*(Q+1)+18)*nm≤b*nm :=
    Nat.mul_le_mul_right nm (by dsimp only [b]; omega)
  have bx : ((36*a+9*(Q+1)+16)+(3*(Q+1)+5)+(3*(Q+1)+5))*ns≤b*ns :=
    Nat.mul_le_mul_right ns (by dsimp only [b]; omega)
  have vM : (3*P+5)*(4*lam)≤b*K := calc
    _≤(3*P+5)*(4*K) := Nat.mul_le_mul_left _ (by omega)
    _=((3*P+5)*4)*K := by ring
    _≤_ := Nat.mul_le_mul_right K (by dsimp only [b]; omega)
  have bd : (13*key+4)+nativeFieldsFee I.tc I.tz I.tm I.dep prec+
      (2*(3*(Q+1)+1)+21)+J6R30ProducedGateRegistry.contextCopyFee tw bw+
      3*(I₀).val+3*(4*lam)+32+3+8+4≤b := by
    unfold nativeFieldsFee J6R30ProducedGateRegistry.contextCopyFee
    dsimp only [b]
    omega
  obtain ⟨edges,masks⟩ := true_first_edge_and_mask_census I
  unfold firstReplayTariff chartResidentFee residentFieldsFee activeFieldsFee
  rw [←masks,edges]
  change (13*key+4)+nativeFieldsFee I.tc I.tz I.tm I.dep prec+
    (2*(3*(Q+1)+1)+21+(39*a+3*(Q+1)+18)*nm+(36*a+9*(Q+1)+16)*ns+
      (3*(Q+1)+5)*ns+(3*(a+((Q-a)+13*a))+51)*ne)+
    (J6R30ProducedGateRegistry.contextCopyFee tw bw+3*(I₀).val+3*(4*lam)+(3*(Q+1)+5)*ns+32)+
    (3+(3*P+5)*(4*lam))+8+4≤b*(1+K+ne+nm+ns)
  rw [Nat.add_mul,Nat.add_mul] at bx
  calc
    _≤b+b*K+b*ne+b*nm+b*ns := by omega
    _=_ := by ring

#print axioms true_first_edge_and_mask_census
#print axioms exact_first_copy_tariff_bounded_by_true_widths
end
end J6R68RateJoint.RootWords

