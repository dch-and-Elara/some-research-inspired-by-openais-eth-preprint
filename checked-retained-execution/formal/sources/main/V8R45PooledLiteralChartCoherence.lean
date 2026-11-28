import V8R45PooledLiteralDispatch

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
set_option maxRecDepth 2400

namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketScopes J6R11Blueprint
noncomputable section
variable {E A B : Type} [Fintype E] [Fintype A] [Fintype B]
variable {N : Network E A B} {f : ℤ[X]} {a p : ℕ}

def alignMode {P Q : PhysicalPacking N a (Fin 64)} {i j : Fin a}
    (hP : P=Q) (hi : i=j) : Mode i p P.mask ≃ Mode j p Q.mask := by
  subst Q
  subst j
  exact Equiv.refl _

omit [Fintype E] [Fintype A] [Fintype B] in
theorem align_mode_keeps_menu {P Q : PhysicalPacking N a (Fin 64)} {i j : Fin a}
    (hP : P=Q) (hi : i=j) (β : Mode i p P.mask →₀ ℕ) :
    Finsupp.embDomain (alignMode hP hi).toEmbedding β ∈
      J6RecursiveMenu.menu p (J6R10RowAffine.weight j p Q.mask) ↔
    β ∈ J6RecursiveMenu.menu p (J6R10RowAffine.weight i p P.mask) := by
  subst Q
  subst j
  have eq : Finsupp.embDomain (alignMode rfl rfl).toEmbedding β = β := by
    ext m
    exact Finsupp.embDomain_apply (Equiv.refl _).toEmbedding β m
  rw [eq]

theorem align_mode_keeps_packet {P Q : PhysicalPacking N a (Fin 64)} {i j : Fin a}
    (hP : P=Q) (hi : i=j) {t : ℤ} (ht : t≠0)
    (hvi : padicValInt 2 t=i.val) (hvj : padicValInt 2 t=j.val)
    (z : Residue f 1 p) (F : EntryFile f 1 N) (β : Mode i p P.mask →₀ ℕ) (g : Fin 64) :
    actualPacketHost Q j ht hvj p (J6R10Integral.box_two_nil p f 1) z F
      (Finsupp.embDomain (alignMode hP hi).toEmbedding β) g =
    actualPacketHost P i ht hvi p (J6R10Integral.box_two_nil p f 1) z F β g := by
  subst Q
  subst j
  have eq : Finsupp.embDomain (alignMode rfl rfl).toEmbedding β = β := by
    ext m
    exact Finsupp.embDomain_apply (Equiv.refl _).toEmbedding β m
  rw [eq]

theorem change_receiving_index {R : ℕ → Type*} {p q : ℕ}
    (e : p=q) (x : R p) (y : R q) (h : cast (congrArg R e) x=y) :
    x = cast (congrArg R e.symm) y := by
  subst q
  exact h

#print axioms align_mode_keeps_menu
#print axioms align_mode_keeps_packet
#print axioms change_receiving_index
end

end V8R45PooledLiteral