import V8NativeMessageN4OrdinaryFit
import V8NativeMessageN4LiteralD
import V8NativeMessageC3CanonicalAssembly

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000

/-! Exact original ordinary MAIN and D coefficients on the true
four-copy slot, and preservation of the terminal full precision by
termwise replacement. No nonlinear or extra fractional operation is
folded into the audited ordinary coefficient. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal J6R9Recursive J6R10Repack V8NativeMessage.C3.Canonical
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
variable {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}
variable {P : RootPacking F reg f} {d : LayoutReady F reg f} {i : rootKept F f}

structure OrdinaryQuery (P : RootPacking F reg f) (d : LayoutReady F reg f) (i : rootKept F f) where
  groups : ℕ
  nodes : ℕ
  order : ℕ
  degree : ℕ
  bp : ℕ
  beta : ℕ
  tuple : CloneTuple F groups nodes order
  accepted : feasible tuple.frame
  pointList : N6.FixedLists tuple
  legalRows : N1.RowBound tuple reg degree bp
  legalWeights : ∀ g j, pointList.weight g j∈C3.RawMain.localJetImage order
  printedNodes : nodes=mainPrintedQ (Fintype.card W)
  printedDegree : degree=mainPrintedR (Fintype.card W) beta
  printedOrder : order=mainPrintedJ (Fintype.card W) degree nodes
  betaPos : 1≤beta
  separation : 6*degree≤nodes
  slot : PublicSlot F reg f P d
  sameCoordinate : atCenter d slot.1=i

variable (B : OrdinaryQuery P d i) (hf : f.Monic)

def ordinaryM (σ : W→Bool) : RatRing f 1 :=
  algebraMap ℚ (RatRing f 1) (fourMainOrigin B.tuple reg B.accepted B.pointList σ)

def ordinaryD : RatRing f 1 := publicMenuWeight F reg f d B.slot.1 B.slot.2.1

def weightedWhole (σ : W→Bool) : RatRing f 1 :=
  (ordinaryD B*ordinaryM B σ)*embed f 1 (rawWhole d hf B.slot σ)

def weightedSeparate (σ : W→Bool) : RatRing f 1 :=
  (ordinaryD B*ordinaryM B σ)*embed f 1 (rawSeparate d hf B.slot σ)

theorem original_ordinary_term_safe (σ : W→Bool) :
    ∃ e : IntRing f 1, weightedWhole B hf σ-weightedSeparate B hf σ =
      embed f 1 ((2:IntRing f 1)^(4*Fintype.card W+1)*e) := by
  have hJ : 0<B.order := by
    rw [B.printedOrder]
    exact Nat.add_pos_left (by decide : 0<1) _
  have hQ : 0<B.nodes := Nat.zero_lt_of_lt B.tuple.node.isLt
  have hMain := four_main_origin_loss B.tuple reg B.legalRows B.accepted B.pointList
    hJ B.legalWeights f σ
  have hD := literal_D_probe_loss d B.slot.1 B.slot.2.1
  have hFit := actual_four_main_reserve d B.slot.1 B.degree B.nodes B.order B.beta
    hQ B.printedNodes B.betaPos B.printedDegree B.separation B.printedOrder
  simp only [weightedWhole,weightedSeparate,← mul_sub]
  exact literal_whole_loss_exchange d hf B.slot _ _ _ _ hMain hD σ
    (hFit.trans (Nat.le_add_right _ _)) le_rfl

variable {H : Type*} [Fintype H]

theorem original_ordinary_assembly_safe (blocks : H→OrdinaryQuery P d i) (σ : W→Bool)
    (A : IntRing f 1) (correct : (∑ h, weightedWhole (blocks h) hf σ)=embed f 1 A) :
    ∃ A' : IntRing f 1,
      (∑ h, weightedSeparate (blocks h) hf σ)=embed f 1 A' ∧
      reduce (4*Fintype.card W+1) f 1 A'=reduce (4*Fintype.card W+1) f 1 A :=
  assemble_replacements hf (fun h => weightedWhole (blocks h) hf σ)
    (fun h => weightedSeparate (blocks h) hf σ) A correct
    (fun h => original_ordinary_term_safe (blocks h) hf σ)

#print axioms original_ordinary_term_safe
#print axioms original_ordinary_assembly_safe
end
end V8NativeMessage.N4
