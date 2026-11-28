import P5D1LiteralOldRows
import P5HybridClosureActual
import J6R12BlueprintFactory

/-! Sign locality concerns the literal, newly wired child host with an
immutable file and per-entry creation precision. It holds for each common
public signed center, binary probe and legal mode, before contraction. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial
open Polynomial J6R10Repack P11FullPacking J6R9PacketScopes J6R9Recursive
open J6R11Blueprint Paper5.HybridClosure

section Generic
variable {E A B K G : Type} {f : ℤ[X]} {ell : ℕ}

theorem compileChild_equal_at_group (N : Network E A B) (group : A ⊕ B → G)
    (packet : E → K) (g : G) (F F' : EntryFile f ell N) (p : ℕ)
    (packetValue : ∀ k : K, (PacketPorts N group packet g k → Bool) → Residue f ell p)
    (agree : ∀ v : Old group g, F v.val = F' v.val) :
    compileChild N group packet g F p packetValue =
      compileChild N group packet g F' p packetValue := by
  funext v
  cases v with
  | inl v =>
    change (F v.val).reindex _ = (F' v.val).reindex _
    rw [agree v]
  | inr k => rfl

theorem packet_host_equal_at_group [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ} (ht : t ≠ 0)
    (hv : padicValInt 2 t = i.val) (p : ℕ) (hnil : (2:Residue f ell p)^p=0)
    (z : Residue f ell p) (F F' : EntryFile f ell N)
    (β : Mode i p P.mask →₀ ℕ) (g : G)
    (agree : ∀ v : Old (atGroup P i) g, F v.val = F' v.val) :
    actualPacketHost P i ht hv p hnil z F β g =
      actualPacketHost P i ht hv p hnil z F' β g := by
  unfold actualPacketHost physicalChildHost
  rw [compileChild_equal_at_group _ _ _ _ _ _ _ _ agree]
end Generic

section Old
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
local notation "N" => dNetwork F cubic

abbrev PinSlice {a : ℕ} (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (g : Fin 64) :=
  {v : W // P.rowLabel (.inr (.inl v)) i = g}

theorem oldRow_file_equal_at_group {f : ℤ[X]} (p₀ : ℕ)
    {a : ℕ} (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (g : Fin 64)
    (σ τ : W → Bool) (agree : ∀ v : PinSlice F cubic P i g, σ v.val = τ v.val) :
    ∀ v : Old (atGroup P i) g,
      oldRowFile F cubic f p₀ σ v.val = oldRowFile F cubic f p₀ τ v.val := by
  rintro ⟨v,hv⟩
  by_cases h : ∃ w : W, v = .inl (.inr (.inl w))
  · obtain ⟨w,rfl⟩ := h
    exact oldRow_pin_file_congr F cubic f p₀ σ τ w (agree ⟨w,hv⟩)
  · apply oldRow_pure_file_congr
    exact fun w hw => h ⟨w,hw⟩

theorem oldRow_child_group_local {f : ℤ[X]} (p₀ : ℕ)
    {a : ℕ} (P : PhysicalPacking N a (Fin 64)) (i : Fin a) {t : ℤ} (ht : t ≠ 0)
    (hv : padicValInt 2 t = i.val) (p : ℕ) (hnil : (2:Residue f 1 p)^p=0)
    (z : Residue f 1 p) (β : Mode i p P.mask →₀ ℕ) (g : Fin 64)
    (σ τ : W → Bool) (agree : ∀ v : PinSlice F cubic P i g, σ v.val = τ v.val) :
    actualPacketHost P i ht hv p hnil z (oldRowFile F cubic f p₀ σ) β g =
      actualPacketHost P i ht hv p hnil z (oldRowFile F cubic f p₀ τ) β g :=
  packet_host_equal_at_group P i ht hv p hnil z _ _ β g (oldRow_file_equal_at_group F cubic p₀ P i g σ τ agree)

noncomputable def extendSign {a : ℕ} (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    (g : Fin 64) (bits : PinSlice F cubic P i g → Bool) (v : W) : Bool :=
  if h : P.rowLabel (.inr (.inl v)) i = g then bits ⟨v,h⟩ else false

/-- All contracted child bits are functions of sign bits on the precise
old-row group of the same physical packing; no read of any other sign
is inherent in the local response. Actual new packet tables do not use signs. -/
theorem oldRow_child_from_local_bits {f : ℤ[X]} (p₀ : ℕ)
    {a : ℕ} (P : PhysicalPacking N a (Fin 64)) (i : Fin a) {t : ℤ} (ht : t ≠ 0)
    (hv : padicValInt 2 t = i.val) (p : ℕ) (hnil : (2:Residue f 1 p)^p=0)
    (z : Residue f 1 p) (β : Mode i p P.mask →₀ ℕ) (g : Fin 64)
    (σ : W → Bool) :
    actualPacketHost P i ht hv p hnil z (oldRowFile F cubic f p₀ σ) β g =
      actualPacketHost P i ht hv p hnil z
        (oldRowFile F cubic f p₀ (extendSign F cubic P i g fun v => σ v.val)) β g := by
  apply oldRow_child_group_local
  intro v
  simp only [extendSign, dif_pos v.property]
end Old

/-- The source group is exactly the slice of the E1 old-row label, not
the reverse orientation used for the J9 column-erasure examples. -/
theorem e1_pinSlice_is_E1_label {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (cubic : ∀ v, GraphCutMoments.degree E v=3)
    (loopless : ∀ v,(v,v)∉E) {a : ℕ}
    (P : PhysicalPacking (dNetwork (replacedEdges E cubic) (replaced_cubic E cubic loopless))
      a (Fin 64))
    (kept : Finset (Fin a)) (i : kept) (g : Fin 64) :
    PinSlice (replacedEdges E cubic) (replaced_cubic E cubic loopless) P i.val g =
      {v : TriVertex V // DPinLabels E cubic loopless P kept v i = g} := rfl

#print axioms e1_pinSlice_is_E1_label
#print axioms compileChild_equal_at_group
#print axioms packet_host_equal_at_group
#print axioms oldRow_file_equal_at_group
#print axioms oldRow_child_group_local
#print axioms oldRow_child_from_local_bits
end Paper5.D1Literal
