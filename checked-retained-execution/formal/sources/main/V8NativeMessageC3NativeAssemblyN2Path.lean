import V8NativeMessageC3NativeAssemblyN2Descent
import J6R12IntegralDirectPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

/-! Bind structural descent to the emitted native packet factory.
The selected slot preserves its same centre, probe and mode tuple. -/
namespace V8NativeMessage.C3.NativeAssembly
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Reachable J6ActiveRun J6R12Blueprint J6R11Blueprint
  J6R9Recursive J1PPrinted J6ActiveSchedule P1DyadicGrid
noncomputable section

theorem native_address_from_taper {H : Type*} (N : NativeShape H) (c : Call H)
    (ha : N.params.cutoff<c.edges) (hu : 0<N.params.levelWidth c.depth)
    (hua : N.params.levelWidth c.depth≤N.params.levelBits c.depth)
    (huM : N.params.levelWidth c.depth≤c.edges) (hw : ∀ t m, 0<N.weight c t m) :
    Nonempty (LiveAddress N c) := by
  have hA : 1≤N.params.levelBits c.depth := hu.trans_le hua
  have hOne : (1:ℤ)∈oddGrid (N.params.levelBits c.depth) := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_grid.mpr ⟨by have := pow₂_pos (N.params.levelBits c.depth); omega,?_⟩, by decide⟩
    obtain ⟨a,he⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hA)
    rw [he,pow₂_succ]
    have := pow₂_pos a
    omega
  let t : Center N.params c := ⟨1,oddGrid_subset_active _ _ _ hu huM hOne⟩
  let z : Probe N.params c := ⟨0,Nat.succ_pos _⟩
  letI : Fintype (N.Mode c t) := N.finiteMode c t
  letI : DecidableEq (N.Mode c t) := N.decideMode c t
  have hp : 0<registerPrecision N.params c t :=
    (Nat.zero_le c.prec).trans_lt (child_monotone _ _ _ _ _ (Nat.zero_lt_of_lt ha))
  let β : NativeMenu N c t := ⟨0,J6RecursiveMenu.zero_in_menu _ hp _ (hw t)⟩
  exact ⟨⟨⟨t,z,β,0⟩,ha⟩⟩

variable {f : ℤ[X]} {ell : ℕ}
section GenericFactory
variable {S : Params (f:=f) (ell:=ell)} {Δ : ℕ} (sel : Selector S Δ)

abbrev FactoryPlan := nativePlan (shape S Δ sel) (children S Δ sel)

def regroupNative (c : Call (PhysicalHost f ell)) (w : LiveAddress (shape S Δ sel) c)
    (g : Fin 64) : LiveAddress (shape S Δ sel) c :=
  Subtype.mk (Sigma.mk w.val.1 (w.val.2.1,(w.val.2.2.1,g))) w.property

theorem regroup_edgeCount (c : Call (PhysicalHost f ell))
    (w : LiveAddress (shape S Δ sel) c) (d : Ready S Δ c) (g : Fin 64) :
    ((FactoryPlan sel).child c (regroupNative sel c w g)).edges =
      (packetOfSite sel d w.val.1 w.val.2.1 (siteTuple sel d w.val) g).edgeCount := by
  change (payload S Δ sel c (regroupNative sel c w g).val).2 = _
  rw [payload_exact sel d]
  rfl

theorem actual_largest_branch (c : Call (PhysicalHost f ell))
    (w : LiveAddress (shape S Δ sel) c) (d : Ready S Δ c) :
    ∃ g : Fin 64, (∀ j, ((FactoryPlan sel).child c (regroupNative sel c w j)).edges ≤
      ((FactoryPlan sel).child c (regroupNative sel c w g)).edges) ∧
      c.edges≤32*((FactoryPlan sel).child c (regroupNative sel c w g)).edges := by
  obtain ⟨g,hg,hlo,_⟩ := actual_sibling_has_maximum sel d w.val.1 w.val.2.1 (siteTuple sel d w.val)
  exact ⟨g,fun j => by rw [regroup_edgeCount sel c w d j,regroup_edgeCount sel c w d g]; exact hg j,
    by rw [regroup_edgeCount sel c w d g]; exact hlo⟩
end GenericFactory

variable {s C : ℕ} (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))

include cfg in
theorem actual_active_has_address (c : Call (PhysicalHost f ell)) (seed : Stable s C c)
    (ha : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges) :
    Nonempty (LiveAddress (shape (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) sel) c) := by
  let S : Params (f:=f) (ell:=ell) := printedParams s
  have ht := printed_taper_legal s c.edges C c.depth cfg.widthPos cfg.constPos cfg.size ha seed.sizeByDepth
  exact native_address_from_taper (shape S (sourceDelta s) sel) c ha ht.1 ht.2.1 ht.2.2
    (weightAt_pos S (sourceDelta s) sel c)

include cfg in
theorem actual_active_has_large_step (c : Call (PhysicalHost f ell)) (seed : Stable s C c)
    (ha : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges) :
    ∃ w : (FactoryPlan sel).Slot c, Stable s C ((FactoryPlan sel).child c w) ∧
      c.edges≤32*((FactoryPlan sel).child c w).edges := by
  obtain ⟨w⟩ := actual_active_has_address cfg sel c seed ha
  let d : Ready (printedParams s) (sourceDelta s) c := getReady cfg seed ha
  obtain ⟨g,_,hg⟩ := actual_largest_branch sel c w d
  exact ⟨regroupNative sel c w g,stable_step cfg sel seed (regroupNative sel c w g),hg⟩

include cfg in
theorem leaf_from_requested_slot (c : Call (PhysicalHost f ell)) (seed : Stable s C c)
    (w : (FactoryPlan sel).Slot c) :
    ∃ g : Fin 64, (∀ j, ((FactoryPlan sel).child c (regroupNative sel c w j)).edges≤
      ((FactoryPlan sel).child c (regroupNative sel c w g)).edges) ∧
    ∃ d : Call (PhysicalHost f ell),
      NativeReach (FactoryPlan sel) ((FactoryPlan sel).child c (regroupNative sel c w g)) d ∧
      d.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff ∧
      (printedParams (f:=f) (ell:=ell) s).cutoff<32*d.edges := by
  let d : Ready (printedParams s) (sourceDelta s) c := getReady cfg seed w.property
  obtain ⟨g,hm,hg⟩ := actual_largest_branch sel c w d
  let P := FactoryPlan sel
  let H := (printedParams (f:=f) (ell:=ell) s).cutoff
  have hStep : ∀ c', Stable s C c' → H<P.size c' →
      ∃ w' : P.Slot c', Stable s C (P.child c' w') ∧ P.size c'≤32*P.size (P.child c' w') :=
    actual_active_has_large_step cfg sel
  obtain ⟨e,he,_,hl,hs⟩ := reach_large_literal_leaf P H (Stable s C) hStep
    (P.child c (regroupNative sel c w g)) (stable_step cfg sel seed (regroupNative sel c w g))
    (w.property.trans_le hg)
  exact ⟨g,hm,e,he,hl,hs⟩

#print axioms native_address_from_taper
#print axioms regroup_edgeCount
#print axioms actual_largest_branch
#print axioms actual_active_has_address
#print axioms actual_active_has_large_step
#print axioms leaf_from_requested_slot
end
end V8NativeMessage.C3.NativeAssembly
