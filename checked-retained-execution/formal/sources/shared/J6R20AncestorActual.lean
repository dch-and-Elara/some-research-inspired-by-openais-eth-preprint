import J6R20AncestorHost

/-! The R20 one-entry runner specializes directly to the real second
actualPacketHost. Setting the arbitrary sibling values to zero affects only
unqueried new siblings; the equality is solely on the retained file. -/
namespace J6R20Ancestor
open scoped Polynomial
open J6R10Repack J6R11Blueprint P11FullPacking J6R9PacketScopes

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

theorem actual_retained_independent_siblings {f : ℤ[X]} {ell q : ℕ}
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (hnil : (2:Residue f ell q)^q=0) (z : Residue f ell q)
    (old : EntryFile f ell N) (β : Mode i q P.mask→₀ℕ)
    (g : G) (v : Old (atGroup P i) g)
    (other : ∀ k : Page a P.copies G,(PacketPorts N (atGroup P i) (atPacket P) g k→Bool)→Residue f ell q) :
    (actualPacketHost P i ht hv q hnil z old β g).file (.inl v) =
      compileChild N (atGroup P i) (atPacket P) g old q other (.inl v) := rfl

#print axioms actual_retained_independent_siblings
end J6R20Ancestor


