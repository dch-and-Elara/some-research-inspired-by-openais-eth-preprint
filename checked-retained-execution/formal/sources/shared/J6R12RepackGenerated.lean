import J6R12RepackSelection
import J6R12BlueprintPacket

/-! Successor invariant for the actual active call. A generated child has
the printed degree bound and can be labelled and packed anew using its
own incidence. Its installed table descriptors still know which entries
were newly created at p_t and which came from the parent. -/
namespace J6R12Repack
open scoped Classical Polynomial
open J6R10Repack J6R11Repack J6R11Blueprint P11FullPacking J6R9PacketScopes
variable {f : ℤ[X]} {ell : ℕ} {G : Type} [LinearOrder G] [Fintype G]
variable {H : PhysicalHost f ell} {a : ℕ}

set_option maxHeartbeats 1500000 in
theorem generated_degrees (P : PhysicalPacking H.network a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (Δ : ℕ)
    (degree : GoodDegree H Δ) (hL : 2*2^a ≤ Δ) :
    letI := H.finiteEdge
    letI := H.finiteRow
    letI := H.finiteCol
    GoodDegree (actualPacketHost P i ht hv p hnil z H.file β g) Δ := by
  exact printed_child_degrees H.network (atGroup P i) P.seat g degree.1 degree.2 hL

set_option maxHeartbeats 1500000 in
theorem generated_creation_tags (P : PhysicalPacking H.network a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p p_t : ℕ)
    (hnil : (2:Residue f ell p_t)^p_t=0) (z : Residue f ell p_t)
    (β : Mode i p_t P.mask →₀ ℕ) (g : G)
    (older : GoodTags H p) (increases : p≤p_t) :
    letI := H.finiteEdge
    letI := H.finiteRow
    letI := H.finiteCol
    GoodTags (actualPacketHost P i ht hv p_t hnil z H.file β g) p_t := by
  intro v
  change Old (atGroup P i) g ⊕ Page a P.copies G at v
  cases v with
  | inl v => exact (older v.val).trans increases
  | inr k => exact Nat.le_refl _

set_option maxHeartbeats 2000000 in
/-- Repacks the same generated child, not a new abstract graph with an
assumed compatible answer. The numeric packing premises are attached to
its next active schedule, because a leaf needs no fresh packing. -/
theorem generated_can_repack (P : PhysicalPacking H.network a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (a' Δ : ℕ)
    (hG : Fintype.card G=64) (degree : GoodDegree H Δ) (hL : 2*2^a ≤ Δ) :
    letI := H.finiteEdge
    letI := H.finiteRow
    letI := H.finiteCol
    let C := actualPacketHost P i ht hv p hnil z H.file β g
    2*(J9PrintedSchedule.arrayCard a')^2*Δ ≤ C.edgeCount →
    2^a'*J9PrintedSchedule.arrayCard a' ≤ C.edgeCount →
    ∃ new : PhysicalPacking C.network a' G, new.copies =
      ceilCopies (2^a') (maxFiber (declaredCell C.network new.rowLabel new.colLabel)) := by
  dsimp only
  intro hcol hslot
  exact host_can_repack _ a' Δ hG (generated_degrees P i ht hv p hnil z β g Δ degree hL) hcol hslot

set_option maxHeartbeats 1800000 in
theorem generated_edge_budget (P : PhysicalPacking H.network a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (β : Mode i p P.mask →₀ ℕ) (g : G)
    (hG : Fintype.card G=64) (hH : 0 < H.edgeCount) :
    letI := H.finiteEdge
    letI := H.finiteRow
    letI := H.finiteCol
    let C := actualPacketHost P i ht hv p hnil z H.file β g
    32*C.edgeCount ≤ 3*H.edgeCount ∧ 8*C.edgeCount ≤ H.edgeCount ∧
      C.edgeCount < H.edgeCount := by
  letI := H.finiteEdge
  letI := H.finiteRow
  letI := H.finiteCol
  dsimp only
  have h : 32*(actualPacketHost P i ht hv p hnil z H.file β g).edgeCount ≤ 3*H.edgeCount :=
    actualPacketHost_shrinks P i ht hv p hnil z H.file β g hG hH
  exact ⟨h,by omega,by omega⟩

set_option maxHeartbeats 1800000 in
/-- The legitimate next-degree and inherited per-entry precision state
belong to the same actual child used by every native address. -/
theorem generated_invariants (P : PhysicalPacking H.network a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p p_t : ℕ)
    (hnil : (2:Residue f ell p_t)^p_t=0) (z : Residue f ell p_t)
    (β : Mode i p_t P.mask →₀ ℕ) (g : G) (Δ : ℕ)
    (hG : Fintype.card G=64) (hH : 0 < H.edgeCount)
    (degree : GoodDegree H Δ) (hL : 2*2^a ≤ Δ)
    (older : GoodTags H p) (increases : p≤p_t) :
    letI := H.finiteEdge
    letI := H.finiteRow
    letI := H.finiteCol
    let C := actualPacketHost P i ht hv p_t hnil z H.file β g
    GoodDegree C Δ ∧ GoodTags C p_t ∧ 32*C.edgeCount≤3*H.edgeCount ∧
      C.edgeCount < H.edgeCount := by
  obtain ⟨hm,_,hs⟩ := generated_edge_budget P i ht hv p_t hnil z β g hG hH
  exact ⟨generated_degrees P i ht hv p_t hnil z β g Δ degree hL,
    generated_creation_tags P i ht hv p p_t hnil z β g older increases,hm,hs⟩

set_option maxHeartbeats 1800000 in
/-- The chosen active layout of the actual next host. Leaf hosts have no
need for a packing. Both guards here come from its next active schedule. -/
noncomputable def generated_selected (P : PhysicalPacking H.network a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)
    (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (β : Mode i p P.mask →₀ ℕ) (g : G) (a' Δ : ℕ)
    (hG : Fintype.card G=64) (degree : GoodDegree H Δ) (hL : 2*2^a ≤ Δ) :
    letI := H.finiteEdge
    letI := H.finiteRow
    letI := H.finiteCol
    let C := actualPacketHost P i ht hv p hnil z H.file β g
    2*(J9PrintedSchedule.arrayCard a')^2*Δ ≤ C.edgeCount →
    2^a'*J9PrintedSchedule.arrayCard a' ≤ C.edgeCount →
    Selected C a' G := by
  let h := generated_can_repack P i ht hv p hnil z β g a' Δ hG degree hL
  dsimp only
  intro hc hs
  exact ⟨(h hc hs).choose,(h hc hs).choose_spec⟩

#print axioms generated_edge_budget
#print axioms generated_invariants
#print axioms generated_selected

#print axioms generated_degrees
#print axioms generated_creation_tags
#print axioms generated_can_repack
end J6R12Repack
