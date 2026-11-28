import J6R11BlueprintNetwork
import J6R10RepackPacketScope

/-! Concrete source child factory at a signed active sample. The host
value is the actual newly wired network and immutable entry file, not
an already evaluated scalar. -/
namespace J6R11Blueprint
open scoped Polynomial BigOperators Classical
open Polynomial J6R10Repack P11FullPacking J6R9PacketScopes J6R9Recursive

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

noncomputable def actualPacketHost (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (old : EntryFile f ell N) (β : Mode i p P.mask →₀ ℕ) (g : G) :
    PhysicalHost f ell :=
  physicalChildHost N (atGroup P i) (atPacket P) g old p
    (compiledPacket P i g p (actualPacket P i ht hv p hnil z β g))

theorem actualPacketHost_shrinks (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (old : EntryFile f ell N) (β : Mode i p P.mask →₀ ℕ) (g : G)
    (groups : Fintype.card G = 64) (hn : 0 < Fintype.card E) :
    32*(actualPacketHost P i ht hv p hnil z old β g).edgeCount ≤ 3*Fintype.card E := by
  obtain ⟨hr,hc⟩ := physical_group_caps P groups i g
  have hshrink := (printed_child_shrink N (atGroup P i) g (Nat.card E)
    (by simpa only [Nat.card_eq_fintype_card] using hn) hr hc).1
  simpa only [actualPacketHost,physicalChildHost,physicalHost,PhysicalHost.edgeCount,
    Nat.card_eq_fintype_card] using hshrink

#print axioms actualPacketHost
#print axioms actualPacketHost_shrinks
end J6R11Blueprint