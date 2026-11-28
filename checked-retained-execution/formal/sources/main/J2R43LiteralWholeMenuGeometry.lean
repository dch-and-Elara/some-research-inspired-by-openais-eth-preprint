import P5D1LiteralAgenda
import P9GuardedPacking
import J9R14LowPrecisionGeometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1800
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

/-! P9 guarded seating on the literal old-row graph. It changes only
orientation masks and addresses, not any signed table or symbol word. -/
namespace J2R43LiteralWholeMenu
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking P9BalancedChart OuterNodePacking
open J6R10Repack J9R14LowPrecisionGeometry
open Paper5.D1Literal Paper5.HybridClosure

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {reg : ∀ v,GraphCutMoments.degree F v=3}
variable {a : ℕ}
local notation "E" => DWire F
local notation "C" => MainClonedCNF.Port F
local notation "N" => dNetwork F reg
local notation "Pack" => PhysicalPacking N a (Fin 64)

/-- In the old-row orientation, each real column owner is literally
one subdivision of the given incidence and has its two true ports. -/
def actualKept [Nonempty C] (P : Pack) (t : ℤ) : Finset C :=
  kept (nativeSeats (fun e : E => P.seat e) (fun e : E => P.seat e))
    Finset.univ (vertexOwner P.seat) t

theorem actual_owner [Nonempty C] (P : Pack) (e : E) :
    vertexOwner P.seat (P.seat e)=e.1 :=
  owner_of_seat P.seat e

theorem actual_old_ports [Nonempty C] (P : Pack) :
    ∀ c : C, c∈(Finset.univ : Finset C) → ∃ e : E, vertexOwner P.seat (P.seat e)=c := by
  intro c _
  exact ⟨(c,false),actual_owner P (c,false)⟩

def cellLoadEmbedding (P : Pack) (c : Cell (Fin a) (Fin 64)) :
    RealFiber (declaredCell N P.rowLabel P.colLabel) c ↪ Fin (P.copies * 2^a) where
  toFun e := (fullSlotChart P.mask (P.seat e.val)).2
  inj' := by
    intro x y he
    apply Subtype.ext
    apply P.seat.injective
    apply (fullSlotChart P.mask).injective
    refine Prod.ext ?_ he
    rw [fullSlotChart_cell,fullSlotChart_cell,P.exactCell,P.exactCell,x.property,y.property]

theorem actual_cell_cap (P : Pack) (c : Cell (Fin a) (Fin 64)) :
    Nat.card (RealFiber (declaredCell N P.rowLabel P.colLabel) c)≤P.copies*2^a :=
  (Nat.card_le_card_of_injective _ (cellLoadEmbedding P c).injective).trans_eq (Nat.card_fin _)

def errBudget (F : Finset (W×W)) (a : ℕ) : ℝ :=
  let A := (Fintype.card (MainClonedCNF.Port F):ℝ)
  let D := (Fintype.card (Cell (Fin a) (Fin 64)):ℝ)
  let L := ((2^a:ℕ):ℝ)
  Real.sqrt (5*(2*A)/L) + Real.sqrt (D*(5*(2*A)/L))

#print axioms actual_owner
#print axioms actual_old_ports
#print axioms actual_cell_cap

end
end J2R43LiteralWholeMenu
