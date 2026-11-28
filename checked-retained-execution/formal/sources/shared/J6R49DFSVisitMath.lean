import J6R49DFSModeTrace

/-! Literal admissibility of every dynamically exposed probe mode.
The cursor position and outer value are reached by the actual loop.
After the exact current 64-group step, the continuation uses that
reply's value and fee, not an arbitrary stored answer. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R48DFS

set_option autoImplicit false
set_option maxRecDepth 2300
set_option maxHeartbeats 5100000

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t
local notation "pₜ" => registerPrecision S c t
local notation "W" => J6R15ModeCost.Word q

theorem legal_emission_from_real_probe
    (F : Frame f pₜ) (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell)
    (child : M→Fin 64→Meter (Block F ell))
    (begin : Pending q I.words.length) (start : (startingCursor I hq).result=some begin)
    (now : Pending q I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (modeUpdate F I hv child) begin
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I hq).steps) now outer fee)
    (v : List W) (z : J6R15ModeCost.State q) (emit : now.pulse.result=.emit v z) :
    ∃ β,decodeAt I v=some β ∧ vectorKey sel d t I β=v.map J6R15ModeCost.Word.val := by
  obtain ⟨Q,hQ,_,trace⟩ := starting_cursor_exact I hq
  have H : begin=Q := Option.some.inj (start.symm.trans hQ)
  subst begin
  have mem := actual_emission_mem_run _ Q _ _ _ trace previous emit
  have pos (w : ℕ) (hm : w∈I.modes.map J6R15ModeCost.modeWeight) : 0<w := by
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp hm
    exact (J6R15ModeCost.modeWeight_bounds m).1
  obtain ⟨len,budget⟩ := (J6R15ModeCost.strictTuples_exact _ _ pos).2 _ |>.mp mem
  exact decode_one_legal_vector I v ⟨len.trans (List.length_map _),budget⟩

theorem probe_halts_after_actual_child
    (F : Frame f pₜ) (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell)
    (child : M→Fin 64→Meter (Block F ell))
    (begin : Pending q I.words.length) (start : (startingCursor I hq).result=some begin)
    (now : Pending q I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (modeUpdate F I hv child) begin
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I hq).steps) now outer fee)
    (v : List W) (z : J6R15ModeCost.State q) (emit : now.pulse.result=.emit v z)
    (β : M) (hβ : decodeAt I v=some β)
    (g : Fin 64) (left : List (Fin 64)) (inner : Block F ell) (feeM : ℕ)
    (grown : GroupPrefix F.hp (child β) (oneM F.hp F.sizePos hv).result
      (oneM F.hp F.sizePos hv).steps (g::left) inner feeM) :
    let mul := mulM F.hp ⟨inner,0⟩ (child β g)
    let product := productCursor F.hp (child β) left mul.result (feeM+mul.steps)
    let sum := addM F.hp ⟨outer,0⟩ product
    let rest := modeDrain (modeUpdate F I hv child) (now.tail emit) sum.result
      (fee+now.pulse.steps+sum.steps)
    runProbe F I hq hv child=⟨rest.result.1,rest.steps⟩ := by
  have P := mode_prefix_continuation _ _ _ _ previous
  have E := drain_next_is_real (modeUpdate F I hv child) now outer fee emit
  have G := real_group_invocation F.hp (child β) _ _ grown
  have C : modeUpdate F I hv child outer v=
      addM F.hp ⟨outer,0⟩ (product64 F.hp F.sizePos hv (child β)) := by
    rw [modeUpdate,hβ]
  dsimp only
  rw [runProbe,start]
  dsimp only
  rw [P,E,C,product64,G]

#print axioms legal_emission_from_real_probe
#print axioms probe_halts_after_actual_child
end J6R49DFS
