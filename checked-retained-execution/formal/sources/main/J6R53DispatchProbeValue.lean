import J6R53DispatchRawProbe

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 12000000
set_option maxRecDepth 2900

/-! No typed decode enters the new loop. For whatever raw provider is
installed, its actual calls are the fold's measured operations. The
old typed semantics are compared only at the proof boundary. -/
namespace J6R53Dispatch
open scoped Polynomial
open AOracleMachineTime A1R12 J6R15ModeCost J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R48DFS J6R49DFS

variable {q : ℕ} {V : Type*}

theorem fold_bytes_same {A B : V→List (Word q)→Meter V} (xs : List (List ℕ))
    (same : ∀ v∈xs,∀ a,A a (v.map word)=B a (v.map word)) (a : V) :
    foldExpected A xs a=foldExpected B xs a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x rest ih =>
    have e := same x List.mem_cons_self a
    have h := ih (fun y hy=>same y (List.mem_cons_of_mem x hy)) ((B a (x.map word)).result)
    simp only [foldExpected,e,h]

variable {f : ℤ[X]} {ell : ℕ} {SP : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable {sel : Selector SP Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready SP Δ c} {t : Center SP c}
local notation "pₜ" => registerPrecision SP c t
local notation "W" => J6R15ModeCost.Word q
local notation "M" => NativeMenu (shape SP Δ sel) c t

theorem exposed_probe_actual_cost (F : Frame f pₜ) (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell)
    (read : List W→Fin 64→Meter (Block F ell)) :
    let init := zeroM (ell:=ell) (f:=F.words) F.hp
    let xs := tupleSpec I
    let model := foldExpected (updateExposed F hv read) xs init.result
    let out := probeExposed F I hq hv read
    out.result=model.result ∧ out.steps ≤ init.steps+(startingCursor I hq).steps+
      model.steps+(xs.length+1)*delayCap q I.words.length := by
  let init := zeroM (ell:=ell) (f:=F.words) F.hp
  obtain ⟨begin,ok,_,trace⟩ := starting_cursor_exact I hq
  obtain ⟨value,fee⟩ := halt_driven_fold_exact begin (tupleSpec I) trace
    (updateExposed F hv read) init.result (init.steps+(startingCursor I hq).steps)
  unfold probeExposed
  dsimp only
  rw [ok]
  dsimp only
  exact ⟨congrArg Prod.fst value,fee⟩

theorem exposed_probe_preserves_literal_values (F : Frame f pₜ) (I : SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (read : List W→Fin 64→Meter (Block F ell))
    (old : M→Fin 64→Meter (Block F ell))
    (same : ∀ β g,read ((vectorKey sel d t I β).map word) g=old β g) :
    (probeExposed F I hq hv read).result=(runProbe F I hq hv old).result := by
  let init := zeroM (ell:=ell) (f:=F.words) F.hp
  obtain ⟨begin,ok,_,trace⟩ := starting_cursor_exact I hq
  obtain ⟨order,_,_,horder⟩ := native_mode_order sel d t I
  have h := (halt_driven_fold_exact begin (tupleSpec I) trace
    (modeUpdate F I hv old) init.result (init.steps+(startingCursor I hq).steps)).1
  have comp : ∀ v∈tupleSpec I,∀ a,
      updateExposed F hv read a (v.map word)=modeUpdate F I hv old a (v.map word) := by
    intro v hv' a
    have e : v∈order.map (vectorKey sel d t I) := horder.symm ▸ hv'
    obtain ⟨β,_,rfl⟩ := List.mem_map.mp e
    rw [mode_update_uses_actual_groups,updateExposed]
    rw [funext (same β)]
  have hFold := fold_bytes_same (tupleSpec I) comp init.result
  rw [(exposed_probe_actual_cost F I hq hv read).1, hFold,runProbe,ok]
  exact (congrArg Prod.fst h).symm

#print axioms fold_bytes_same
#print axioms exposed_probe_actual_cost
#print axioms exposed_probe_preserves_literal_values
end J6R53Dispatch

