import P5HybridDUnclonedGraph
import P5HybridSameRouteTerminal
import J6R9PacketScopes
import J6R10RepackPhysical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13500000

/-! The attributed fee is the existing explicit bucket scan, not the
full Appendix D execution or the cost of finding a packing. -/
namespace Paper5.HybridDUncloned
open scoped Classical BigOperators
open J6R9PacketScopes J6R10Repack Paper5.HybridClosure

noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "reg" => replaced_cubic E baseCubic loopless

theorem literal_uncloned_scan_fee {a : ℕ}
    (P : PhysicalPacking (network F reg) a (Fin 64)) (triangle exterior : Fin a)
    (cT : V→Fin 64) (cE : E→Fin 64)
    (hT : ∀ w,rowGroup P.mask triangle (P.seat (pinWire F w))=mainPinColor cT w)
    (hE : ∀ w,rowGroup P.mask exterior (P.seat (pinWire F w))=dPinColor E baseCubic cE w)
    (σ : TriVertex V→Bool) :
    let scan := sameRouteScan E baseCubic
      (fun w j=>rowGroup P.mask j (P.seat (pinWire F w))) triangle exterior cT cE hT hE σ
    boolAsNat scan.1=PinnedCNF.modelCount (PinnedCNF.formula F σ) ∧
    scan.2=6*Fintype.card (TriVertex V)+129 := by
  obtain ⟨count,fee⟩ := sameRouteScan_exact E baseCubic loopless
    (fun w j=>rowGroup P.mask j (P.seat (pinWire F w))) triangle exterior cT cE hT hE
    (MainClonedCNF.leftSlot F reg) (MainClonedCNF.rightSlot F reg) σ
  rw [MainClonedCNF.modelCount_cloned] at count
  exact ⟨count,by simpa only [Fintype.card_fin,Nat.add_assoc,show 2*(64:ℕ)+1=129 by decide] using fee⟩

#print axioms literal_uncloned_scan_fee
end
end Paper5.HybridDUncloned
