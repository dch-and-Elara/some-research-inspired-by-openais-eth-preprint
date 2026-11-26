import P5HybridDOnlyCloned
import P5HybridSameRouteTerminal
import P5HybridDOnlyNativeSite

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000
set_option maxRecDepth 3500

/-! Original §8 lines 2114–2124, on the cloned D input. Two actual
finite root coordinates, one common EntryFile layout for any sign word,
and no identification of the two section-8 group functions with
individual native coefficients. -/
namespace Paper5.HybridDOnly
open scoped Classical Polynomial BigOperators
open Polynomial P1DyadicGrid P11FullPacking Paper5.HybridClosure
open J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun J6R12Blueprint
open Paper5.D1Literal J6ActiveSchedule J6R9Recursive J1PPrinted
open Paper5.HybridClosure.Printed (dLambda dSize dU dA dCells dL dDelta d_printed_feasible)

section Top

open DiagonalAbundance EmpiricalCutMoments ProductVariance GroupProducts J1MainSourceCollision
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
variable (f : ℤ[X])
local notation "F" => replacedEdges E cubic
local notation "reg" => replaced_cubic E cubic loopless
local notation "DNet" => dNetwork F reg
local notation "N" => Fintype.card (TriVertex V)
local notation "S" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "root" => oldRowRoot F reg f (fun _=>false)
theorem checked_original_cloned_D_only
    (hdeg : f.natDegree=4*dLambda N)
    (hlarge : (2*epsDen)^30*(3:ℕ)^10≤dLambda N)
    (exterior triangle : rootKept F f) (distinct : exterior≠triangle) :
    ∃ (P : RootPacking F reg f) (d : Ready S Δ root)
      (cT : V→Fin 64) (cE : E→Fin 64)
      (tE tT : PublicCenter F reg f)
      (tieE : ∀ p,rootLabels F reg f P p exterior=dPinColor E cubic cE p)
      (tieT : ∀ p,rootLabels F reg f P p triangle=mainPinColor cT p),
      tE≠tT ∧ PublicIndex F reg f d tE=exterior.val ∧ PublicIndex F reg f d tT=triangle.val ∧
      (∀ i t, PublicIndex F reg f d t=i →
        registerPrecision S root t = J9PrintedSchedule.precision (4*N+1)
          (HermiteLoss.sourceH (24*N) ((S).levelWidth 0)) (2^((S).levelBits 0-i.val)) (24*N) ((S).levelBits 0)) ∧
      (∀ p i, J6R9PacketScopes.rowGroup P.mask i.val (P.seat (pinWire E cubic p)) =
        rootLabels F reg f P p i) ∧
      P.copies=ceilCopies (2^((S).levelBits 0)) (maxFiber (declaredCell DNet P.rowLabel P.colLabel)) ∧
      varianceScore (declaredCell DNet P.rowLabel P.colLabel)≤4*(24*(N:ℚ))+3*N ∧
      varianceScore (declaredCell DNet P.rowLabel P.colLabel)≤2*(24*(N:ℚ))*Δ ∧
      (∀ c,load (J6R11Collision.edgeCell (DNet).row (DNet).col (P.rowLabel,P.colLabel)) c ≤
        2*(24*(N:ℚ))/(Fintype.card (Draw (Fin ((S).levelBits 0)) (Fin 64)):ℚ)) ∧
      Nat.card (Page ((S).levelBits 0) P.copies (Fin 64))*2^((S).levelBits 0)≤3*(24*N) ∧
      (∀ j g, Nat.card (rowsIn DNet (declaredGroup P.rowLabel P.colLabel j) g)≤3*(24*N)/64 ∧
        Nat.card (colsIn DNet (declaredGroup P.rowLabel P.colLabel j) g)≤3*(24*N)/64) ∧
      (∀ x,empiricalLaw (rootLabels F reg f P) x≤48*uniformWeight (rootKept F f→Fin 64)) ∧
      (∀ σ, boolAsNat (sameRouteScan E cubic (rootLabels F reg f P)
        triangle exterior cT cE tieT tieE σ).1=clonedCount E cubic loopless σ ∧
        (sameRouteScan E cubic (rootLabels F reg f P) triangle exterior cT cE tieT tieE σ).2=6*N+129) := by
  have hN : 0<N := Fintype.card_pos
  have hmin : 131072≤dLambda N :=
    (show 131072≤(2*epsDen)^30*(3:ℕ)^10 by decide).trans hlarge
  have base := d_printed_feasible N hN hmin
  have size := oldRowSize_eq_dSize F reg
  have bits := oldRow_widths_printed F reg f
  have hΔ : 3≤Δ := by rw [size]; exact base.2.2.1
  have ha : (S).cutoff<Fintype.card (DWire F) := by
    change J9PrintedSchedule.leafThreshold (oldRowSize F) (Nat.clog 2 (oldRowSize F))<_ 
    rw [size,d_physical_wire_count F reg]
    exact base.1
  have hc : 2*(J9PrintedSchedule.arrayCard ((S).levelBits 0))^2*Δ≤24*N := by
    rw [bits.1,size]
    exact base.2.2.2.1
  have hs : 2^((S).levelBits 0)*J9PrintedSchedule.arrayCard ((S).levelBits 0)≤24*N := by
    rw [bits.1]
    exact base.2.2.2.2.1
  let cfg := creating_source_config F reg f hdeg hlarge
  let d : Ready S Δ root := getReady cfg (oldRowRoot_stable F reg f _ hΔ) ha
  obtain ⟨P,cT,cE,he,ht,cp,φ,Φ,loads,pages,groups,dom⟩ :=
    on_same_cloned_D_packing E cubic loopless exterior.val triangle.val
      (fun hh=>distinct (Subtype.ext hh)) (rootKept F f) Δ hΔ hc hs
  obtain ⟨tE,eIdx,_⟩ := true_center_for_retained F reg f d exterior
  obtain ⟨tT,tIdx,_⟩ := true_center_for_retained F reg f d triangle
  have hd : tE≠tT := by
    intro e
    apply distinct
    apply Subtype.ext
    exact eIdx.symm.trans ((congrArg (PublicIndex F reg f d) e).trans tIdx)
  refine ⟨P,d,cT,cE,tE,tT,he,ht,hd,eIdx,tIdx,?_,?_,cp,φ,Φ,loads,pages,groups,dom,?_⟩
  · intro i t hi
    have hx := J6R9Recursive.precision_same (4*N+1) ((S).levelBits 0) (Fintype.card (DWire F)) ((S).levelWidth 0) t.property
    change registerPrecision S root t=_ at hx
    have ih : HermiteLoss.level t.val=i.val := congrArg Fin.val hi
    rw [ih,d_physical_wire_count F reg] at hx
    exact hx
  · intro p i
    exact literal_row_pin_group E cubic loopless P i.val p
  · intro σ
    simpa only [Fintype.card_fin] using
      sameRouteScan_exact E cubic loopless (rootLabels F reg f P) triangle exterior cT cE ht he
        (MainClonedCNF.leftSlot F reg) (MainClonedCNF.rightSlot F reg) σ

end Top

#print axioms checked_original_cloned_D_only
end Paper5.HybridDOnly
