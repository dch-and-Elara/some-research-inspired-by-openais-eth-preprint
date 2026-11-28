import J6R49DFSProbe

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 2500

/-! Actual arithmetic/cursor cost of the R49 streamed probe. Typed
decodeAt is a semantic interpretation, not additional measured binary
processing. Scope/build/retirement work is charged only if in child.steps. -/
namespace J6R49Cost
open scoped Polynomial BigOperators
open AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R32StatefulArithmetic
open J6R48DFS J6R49DFS

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t
local notation "pₜ" => registerPrecision S c t

def perModeArithmetic (e ell p : ℕ) (hp : 0<p) :=
  uvWidth e ell p+64*(mulCap e ell p+2)+(addCap e ell p hp+2)

theorem actual_mode_update_bill (F : Frame f pₜ) (I : SiteTape sel d t q) (hv : 0<ell)
    (child : M → Fin 64 → Meter (Block F ell)) (acc : Block F ell) (β : M) :
    let out := modeUpdate F I hv child acc ((vectorKey sel d t I β).map J6R15ModeCost.word)
    let b := bill (child β) (groupOrder 64)
    b ≤ out.steps ∧ out.steps ≤ b+perModeArithmetic F.words.length ell pₜ F.hp := by
  dsimp only
  rw [mode_update_uses_actual_groups]
  let P := product64 F.hp F.sizePos hv (child β)
  have hA := addM_cost F.hp (⟨acc,0⟩ : Meter (Block F ell)) P
  have ha : P.steps ≤ (addM F.hp ⟨acc,0⟩ P).steps := by
    unfold addM; simp only; omega
  obtain ⟨low,high⟩ := product64_bill F.hp F.sizePos hv (child β)
  change uvWidth F.words.length ell pₜ+bill (child β) (groupOrder 64) ≤ P.steps at low
  change P.steps ≤ uvWidth F.words.length ell pₜ+bill (child β) (groupOrder 64)+_ at high
  change (addM F.hp ⟨acc,0⟩ P).steps ≤ 0+P.steps+addCap F.words.length ell pₜ F.hp+2 at hA
  change bill (child β) (groupOrder 64) ≤ (addM F.hp ⟨acc,0⟩ P).steps ∧
    (addM F.hp ⟨acc,0⟩ P).steps ≤ bill (child β) (groupOrder 64)+perModeArithmetic F.words.length ell pₜ F.hp
  unfold perModeArithmetic
  exact ⟨by omega,by omega⟩

theorem actual_mode_fold_bill (F : Frame f pₜ) (I : SiteTape sel d t q) (hv : 0<ell)
    (child : M → Fin 64 → Meter (Block F ell)) (order : List M) (acc : Block F ell) :
    let out := foldExpected (modeUpdate F I hv child) (order.map (vectorKey sel d t I)) acc
    let b := probeEntryBill order child
    b ≤ out.steps ∧ out.steps ≤ b+order.length*perModeArithmetic F.words.length ell pₜ F.hp := by
  induction order generalizing acc with
  | nil => simp [foldExpected,probeEntryBill]
  | cons β rest ih =>
    let x := modeUpdate F I hv child acc ((vectorKey sel d t I β).map J6R15ModeCost.word)
    obtain ⟨hpLo,hpHi⟩ := actual_mode_update_bill F I hv child acc β
    change bill (child β) (groupOrder 64) ≤ x.steps at hpLo
    change x.steps ≤ bill (child β) (groupOrder 64)+_ at hpHi
    obtain ⟨hLo,hHi⟩ := ih x.result
    simp only [List.map_cons,foldExpected,probeEntryBill,List.sum_cons,List.length_cons,Nat.succ_mul]
    change bill (child β) (groupOrder 64) + probeEntryBill rest child  ≤ 
      x.steps+(foldExpected (modeUpdate F I hv child) (rest.map (vectorKey sel d t I)) x.result).steps ∧
    x.steps+(foldExpected (modeUpdate F I hv child) (rest.map (vectorKey sel d t I)) x.result).steps  ≤ 
      bill (child β) (groupOrder 64) + probeEntryBill rest child+
      (rest.length*perModeArithmetic F.words.length ell pₜ F.hp+perModeArithmetic F.words.length ell pₜ F.hp)
    exact ⟨by omega,by omega⟩

theorem actual_streamed_probe_arithmetic_bill (F : Frame f pₜ) (I : SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (child : M → Fin 64 → Meter (Block F ell)) :
    ∃ order : List M,order.Nodup ∧ (∀ β,β∈order) ∧
      (runProbe F I hq hv child).steps ≤ 
        (16*q+14+4*(I.words.length+1)*(q+1))+
        uvWidth F.words.length ell pₜ+
        probeEntryBill order child+
        order.length*perModeArithmetic F.words.length ell pₜ F.hp+
        (order.length+1)*J6R15ModeCost.delayCap q I.words.length := by
  let init := zeroM (ell:=ell) (f:=F.words) F.hp
  let prep := startingCursor I hq
  obtain ⟨P,hP,hStart,hRun⟩ := starting_cursor_exact I hq
  let W := modeUpdate F I hv child
  let out := modeDrain W P init.result (init.steps+prep.steps)
  obtain ⟨_,hCost⟩ := halt_driven_fold_exact P (tupleSpec I) hRun W init.result (init.steps+prep.steps)
  obtain ⟨order,n,cpl,hOrder⟩ := native_mode_order sel d t I
  have hXs : tupleSpec I=order.map (vectorKey sel d t I) := hOrder.symm
  have hStartFee :=
    (J6R15ModeCost.start_exact hq I.words I.precision).2
  have hEntry := (actual_mode_fold_bill F I hv child order init.result).2
  refine ⟨order,n,cpl,?_⟩
  rw [runProbe,hP]
  change out.steps ≤ _
  change out.steps ≤ init.steps+prep.steps+
    (foldExpected W (tupleSpec I) init.result).steps+
    ((tupleSpec I).length+1)*J6R15ModeCost.delayCap q I.words.length at hCost
  rw [hXs,List.length_map] at hCost
  have hRaw : prep.steps=(J6R15ModeCost.start I.words I.precision).steps := hStart
  have hInit : init.steps=uvWidth F.words.length ell pₜ := rfl
  change (foldExpected W (order.map (vectorKey sel d t I)) init.result).steps ≤ _ at hEntry
  omega

#print axioms actual_mode_update_bill
#print axioms actual_mode_fold_bill
#print axioms actual_streamed_probe_arithmetic_bill
end J6R49Cost

