import J6R49DFSVisitMath

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 10500000
set_option maxRecDepth 2700

/-! The exact cursor already exposes each raw vector to its operation.
Pass that vector directly into the 64-group product, rather than erase
it behind a ghost Finsupp decode. One real pulse is billed by modeDrain;
the invoked reader sees the vector while it is live. -/
namespace J6R53Dispatch
open scoped Polynomial
open AOracleMachineTime A1R12 J6R15ModeCost J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R48DFS J6R49DFS

variable {f : ℤ[X]} {ell : ℕ} {SP : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable {sel : Selector SP Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready SP Δ c} {t : Center SP c}
local notation "pₜ" => registerPrecision SP c t
local notation "W" => J6R15ModeCost.Word q

def updateExposed (F : Frame f pₜ) (hv : 0<ell)
    (read : List W→Fin 64→Meter (Block F ell))
    (acc : Block F ell) (raw : List W) : Meter (Block F ell) :=
  addM F.hp ⟨acc,0⟩ (product64 F.hp F.sizePos hv (read raw))

def probeExposed (F : Frame f pₜ) (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell)
    (read : List W→Fin 64→Meter (Block F ell)) : Meter (Block F ell) :=
  let m := startingCursor I hq
  let u := zeroM (ell:=ell) (f:=F.words) F.hp
  match m.result with
  | none => ⟨u.result,u.steps+m.steps⟩
  | some P =>
    let out := modeDrain (updateExposed F hv read) P u.result (u.steps+m.steps)
    ⟨out.result.1,out.steps⟩

theorem true_exposed_probe_continuation
    (F : Frame f pₜ) (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell)
    (read : List W→Fin 64→Meter (Block F ell))
    (begin : Pending q I.words.length) (start : (startingCursor I hq).result=some begin)
    (now : Pending q I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (updateExposed F hv read) begin
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I hq).steps) now outer fee)
    (raw : List W) (z : State q) (emit : now.pulse.result=.emit raw z)
    (g : Fin 64) (left : List (Fin 64)) (inner : Block F ell) (feeM : ℕ)
    (grown : GroupPrefix F.hp (read raw) (oneM F.hp F.sizePos hv).result
      (oneM F.hp F.sizePos hv).steps (g::left) inner feeM) :
    let mul := mulM F.hp ⟨inner,0⟩ (read raw g)
    let product := productCursor F.hp (read raw) left mul.result (feeM+mul.steps)
    let sum := addM F.hp ⟨outer,0⟩ product
    let rest := modeDrain (updateExposed F hv read) (now.tail emit) sum.result
      (fee+now.pulse.steps+sum.steps)
    probeExposed F I hq hv read=⟨rest.result.1,rest.steps⟩ := by
  have P := mode_prefix_continuation _ _ _ _ previous
  have E := drain_next_is_real (updateExposed F hv read) now outer fee emit
  have G := real_group_invocation F.hp (read raw) _ _ grown
  dsimp only
  rw [probeExposed,start]
  dsimp only
  rw [P,E,updateExposed,product64,G]

theorem exposed_raw_mode_is_legal
    (F : Frame f pₜ) (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell)
    (read : List W→Fin 64→Meter (Block F ell))
    (begin : Pending q I.words.length) (start : (startingCursor I hq).result=some begin)
    (now : Pending q I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (updateExposed F hv read) begin
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I hq).steps) now outer fee)
    (raw : List W) (z : State q) (emit : now.pulse.result=.emit raw z) :
    ∃ β, decodeAt I raw=some β ∧ vectorKey sel d t I β=raw.map J6R15ModeCost.Word.val := by
  obtain ⟨Q,hQ,_,trace⟩ := starting_cursor_exact I hq
  have H : begin=Q := Option.some.inj (start.symm.trans hQ)
  subst begin
  have mem := actual_emission_mem_run _ Q _ _ _ trace previous emit
  have pos (w : ℕ) (hm : w∈I.modes.map J6R15ModeCost.modeWeight) : 0<w := by
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp hm
    exact (J6R15ModeCost.modeWeight_bounds m).1
  obtain ⟨len,budget⟩ := (strictTuples_exact _ _ pos).2 _ |>.mp mem
  exact decode_one_legal_vector I raw ⟨len.trans (List.length_map _),budget⟩

#print axioms updateExposed
#print axioms probeExposed
#print axioms true_exposed_probe_continuation
#print axioms exposed_raw_mode_is_legal
end J6R53Dispatch

