
import J6R12BlueprintReach

/-! Costing leaves cannot assume at most twice as many vertices as
live edges: the actual constructor keeps empty packet columns and can
retain a zero-degree old vertex. Charge all of them using a physical
vertex/edge potential along the same native R12 recursion. -/
namespace J6R21Leaf
open scoped Polynomial BigOperators Classical
open Polynomial J6ActiveRun J6R9Recursive J6R10Repack J6R10Reachable
open J6R11Blueprint J6R12Blueprint P11FullPacking J6R9PacketScopes J1PPrinted
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8500000

noncomputable def vertexCount {f : ℤ[X]} {ell : ℕ} (H : PhysicalHost f ell) : ℕ :=
  Nat.card H.Row+Nat.card H.Col

theorem actual_packet_vertex_growth
    {f : ℤ[X]} {ell : ℕ} (H : PhysicalHost f ell) {a : ℕ}
    (P : PhysicalPacking H.network a (Fin 64)) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t = i.val)
    (p : ℕ) (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (β : Mode i p P.mask→₀ℕ) (g : Fin 64) :
    letI := H.finiteEdge
    letI := H.finiteRow
    letI := H.finiteCol
    vertexCount (actualPacketHost P i ht hv p hnil z H.file β g)
      ≤ vertexCount H+3*H.edgeCount := by
  letI := H.finiteEdge
  letI := H.finiteRow
  letI := H.finiteCol
  change Nat.card (Old (atGroup P i) g)+Nat.card (Page a P.copies (Fin 64)) ≤
    Nat.card H.Row+Nat.card H.Col+3*H.edgeCount
  have old : Nat.card (Old (atGroup P i) g) ≤ Nat.card H.Row+Nat.card H.Col := by
    rw [← Nat.card_sum]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have slots := P.paddedBudget
  rw [← total_slots P.mask] at slots
  have count : Nat.card H.Edge=H.edgeCount := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have pg : Nat.card (Page a P.copies (Fin 64))≤3*H.edgeCount := by
    rw [count] at slots
    exact (Nat.le_mul_of_pos_right _ (by positivity : 0<(2:ℕ)^a)).trans slots
  exact Nat.add_le_add old pg

theorem native_vertex_potential_step {f : ℤ[X]} {ell s C : ℕ}
    (cfg : RootBounds s C f)
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {c : Call (PhysicalHost f ell)} (hc : Stable s C c) (w : LiveAddress (N sel) c) :
    vertexCount ((Plan sel).child c w).host + 4*((Plan sel).child c w).edges ≤
      vertexCount c.host + 4*c.edges := by
  let S := printedParams (f:=f) (ell:=ell) s
  let d := getReady cfg hc w.property
  let P := packing sel d
  let t := w.val.1
  let p := registerPrecision S c t
  let i := centerIndex d t
  let β := siteTuple sel d w.val
  let z := w.val.2.1
  let g := w.val.2.2.2
  let new := packetOfSite sel d t z β g
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  have hM : 0<Fintype.card c.host.Edge := by
    change 0<c.host.edgeCount
    rw [d.edgeCount]
    exact Nat.zero_lt_of_lt d.active
  have grow := actual_packet_vertex_growth c.host P i (centerNonzero t) rfl p
    (J6R10Integral.box_two_nil p f ell) (sampleNode S f ell c d.fit t z) β g
  change vertexCount new ≤ vertexCount c.host+3*c.host.edgeCount at grow
  rw [d.edgeCount] at grow
  have shrink := actualPacketHost_shrinks P i (centerNonzero t) rfl p
    (J6R10Integral.box_two_nil p f ell) (sampleNode S f ell c d.fit t z) c.host.file β g
    (Fintype.card_fin 64) hM
  change 32*new.edgeCount≤3*c.host.edgeCount at shrink
  rw [d.edgeCount] at shrink
  rw [show (Plan sel).child c w=⟨new,c.depth+1,new.edgeCount,p⟩ from child_exact sel d w.val]
  change vertexCount new+4*new.edgeCount≤vertexCount c.host+4*c.edges
  omega

theorem native_vertex_potential_reachable {f : ℤ[X]} {ell s C : ℕ}
    (cfg : RootBounds s C f)
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {r c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (seed : Stable s C r) :
    vertexCount c.host+4*c.edges≤vertexCount r.host+4*r.edges := by
  induction h with
  | reflexive => exact le_rfl
  | step w prev ih =>
    exact (ih (stable_step cfg sel seed w)).trans (native_vertex_potential_step cfg sel seed w)

theorem native_vertex_cap {f : ℤ[X]} {ell s C : ℕ}
    (cfg : RootBounds s C f)
    (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    {r c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (seed : Stable s C r) :
    vertexCount c.host≤vertexCount r.host+4*r.edges :=
  (Nat.le_add_right _ _).trans (native_vertex_potential_reachable cfg sel h seed)

#print axioms actual_packet_vertex_growth
#print axioms native_vertex_potential_step
#print axioms native_vertex_potential_reachable
#print axioms native_vertex_cap
end J6R21Leaf
