import J4R43LiteralOutsidePhysicalSupply
import V8NativeMessageN7LiteralSupportOrientation
import P5HybridClosureDPack

/-! Retain the existing certified exterior-pair vertex labels when
moving the same four-clone incidence graph to the old-column
orientation. Every ordered cell census is transported exactly. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3800000

variable {G : Type} [LinearOrder G] [Fintype G] {a : ℕ}

def swapCell : Equiv.Perm (Cell (Fin a) G) :=
  Equiv.piCongrRight (fun _=>Equiv.prodComm G G)

@[simp] theorem swap_cell_twice (c : Cell (Fin a) G) : swapCell (swapCell c)=c := by
  funext i
  rfl

variable {E A B : Type} [Fintype E] {N : Network E A B}
variable (P : PhysicalPacking N a G)

abbrev originalLabel := declaredCell N P.rowLabel P.colLabel
abbrev flippedLabel := declaredCell (swapNetwork N) P.colLabel P.rowLabel

theorem flip_label_actual (e : E) : flippedLabel P e = swapCell (originalLabel P e) := rfl

theorem flip_fiber_card (c : Cell (Fin a) G) :
    Nat.card (Fiber (flippedLabel P) c)=Nat.card (InputCell P (swapCell c)) := by
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun e=>?_
  rw [flip_label_actual]
  constructor
  · intro H
    exact (swap_cell_twice _).symm.trans (congrArg swapCell H)
  · intro H
    exact (congrArg swapCell H).trans (swap_cell_twice _)

def transposePacking : PhysicalPacking (swapNetwork N) a G :=
  let cap (c : Cell (Fin a) G) : Nat.card (Fiber (flippedLabel P) c)≤P.copies*2^a := by
    rw [flip_fiber_card]
    exact same_cell_capacity P _
  ⟨P.colLabel,P.rowLabel,P.copies,fun _ _ _=>false,
    seatReal (fun _ _ _=>false) (flippedLabel P) cap (fun _=>Equiv.refl _),
    seatReal_preserves _ _ _ _,P.paddedBudget⟩

theorem equal_transposed_census (c : Cell (Fin a) G) :
    Nat.card (InputCell (transposePacking P) c)=Nat.card (InputCell P (swapCell c)) :=
  flip_fiber_card P c

theorem same_post_transpose_quota (d : ℕ) (pin : E)
    (hc : 0<P.copies) (left : ∀ v : A,Nat.card {e : E//N.row e=v}≤d)
    (right : ∀ v : B,Nat.card {e : E//N.col e=v}≤d)
    (loaded : ∀ c : Cell (Fin a) G, fullLoad P+2*starWidth d≤2*Nat.card (InputCell P c))
    (scale : 64*(reciprocal d)^2*(starWidth d)^2*Nat.card E≤(fullLoad P)^2) :
    Nonempty (BandSupply (transposePacking P) (printedBand a d) pin) := by
  apply printed_band_from_real_cell_loads (transposePacking P) pin d hc right left
  · intro c
    rw [equal_transposed_census]
    exact loaded _
  · exact scale

#print axioms swap_cell_twice
#print axioms flip_label_actual
#print axioms flip_fiber_card
#print axioms transposePacking
#print axioms equal_transposed_census
#print axioms same_post_transpose_quota
end
end J4R43LiteralOutside

