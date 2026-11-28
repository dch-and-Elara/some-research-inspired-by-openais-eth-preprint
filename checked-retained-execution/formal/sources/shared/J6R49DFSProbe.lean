import J6R49DFSDecode
import J6R49DFSCursor
import J6R32StatefulArithmeticFrameWords

/-! The tape's next actual emission is interpreted once, then feeds
the real 64-group product. The arithmetic/range proof uses a ghost
full order only to compare with the previous mathematical schedule. -/
namespace J6R49DFS
open scoped Polynomial BigOperators
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R32StatefulArithmetic
open J6R48DFS

set_option autoImplicit false
set_option maxRecDepth 2400
set_option maxHeartbeats 6500000

theorem weighted_component_le (ws es : List ℕ)
    (positive : ∀ w∈ws,0<w) (hl : es.length=ws.length) (a : ℕ) (mem : a∈es) :
    a≤J6R15ModeCost.weightedDegree ws es := by
  induction ws generalizing es with
  | nil => cases es <;> simp at hl mem
  | cons w ws ih =>
    cases es with
    | nil => simp at mem
    | cons e es =>
      have hp := positive w List.mem_cons_self
      have len : es.length=ws.length := Nat.succ.inj hl
      rcases List.mem_cons.mp mem with here | later
      · subst e
        change a≤w*a+J6R15ModeCost.weightedDegree ws es
        exact (Nat.le_mul_of_pos_left a hp).trans (Nat.le_add_right _ _)
      · have h := ih es (fun x hx=>positive x (List.mem_cons_of_mem _ hx)) len later
        exact h.trans (Nat.le_add_left _ _)

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t
local notation "pₜ" => registerPrecision S c t

theorem actual_legal_coordinates_fit (I : SiteTape sel d t q) (β : M) :
    ∀ j∈vectorKey sel d t I β,j<2^q := by
  letI := (shape S Δ sel).finiteMode c t
  letI := (shape S Δ sel).decideMode c t
  have hp (m : (shape S Δ sel).Mode c t) : 0<(shape S Δ sel).weight c t m := by
    rw [site_mode_weight sel d t]
    exact (J6R15ModeCost.modeWeight_bounds _).1
  have bound : J6R15ModeCost.weightedDegree (I.modes.map J6R15ModeCost.modeWeight)
      (vectorKey sel d t I β)<pₜ := by
    unfold vectorKey
    rw [roster_is_menu_weight (site_mode_equiv sel d t) ((shape S Δ sel).weight c t)
      J6R15ModeCost.modeWeight (site_mode_weight sel d t) I.modes I.nodup I.allModes]
    exact (J6RecursiveMenu.exact_printed_menu _ _ hp β.val).mp β.property
  have hpos (w : ℕ) (mem : w∈I.modes.map J6R15ModeCost.modeWeight) : 0<w := by
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp mem
    exact (J6R15ModeCost.modeWeight_bounds m).1
  have hP : pₜ<2^q := I.precisionMeaning ▸ J6R15ModeCost.val_lt I.precision
  intro j hj
  exact ((weighted_component_le _ _ hpos (by simp only [vectorKey,List.length_map]) j hj).trans_lt bound).trans hP

/-- One mode's semantic label is decoded once and reused across all
64 calls. Its Nat/Finsupp interpretation is not priced here. -/
noncomputable def modeUpdate (F : Frame f pₜ) (I : SiteTape sel d t q) (hv : 0<ell)
    (child : M→Fin 64→Meter (Block F ell))
    (acc : Block F ell) (raw : List (J6R15ModeCost.Word q)) : Meter (Block F ell) :=
  match decodeAt I raw with
  | none => ⟨acc,0⟩
  | some β => addM F.hp ⟨acc,0⟩ (product64 F.hp F.sizePos hv (child β))

theorem mode_update_uses_actual_groups (F : Frame f pₜ) (I : SiteTape sel d t q) (hv : 0<ell)
    (child : M→Fin 64→Meter (Block F ell)) (acc : Block F ell) (β : M) :
    modeUpdate F I hv child acc ((vectorKey sel d t I β).map J6R15ModeCost.word)=
      addM F.hp ⟨acc,0⟩ (product64 F.hp F.sizePos hv (child β)) := by
  rw [modeUpdate,decode_canonical_mode_words I β (actual_legal_coordinates_fit I β)]

theorem fold_typed_mode_output (F : Frame f pₜ) (I : SiteTape sel d t q) (hv : 0<ell)
    (child : M→Fin 64→Meter (Block F ell)) (order : List M) (acc : Block F ell) :
    uvRead F.hp F.words ell (foldExpected (modeUpdate F I hv child)
        (order.map (vectorKey sel d t I)) acc).result =
      uvRead F.hp F.words ell acc+
        (order.map (fun β=>∏ g : Fin 64,uvRead F.hp F.words ell (child β g).result)).sum := by
  induction order generalizing acc with
  | nil => simp only [List.map_nil,foldExpected,List.sum_nil,add_zero]
  | cons β rem ih =>
    simp only [List.map_cons,foldExpected]
    rw [ih,mode_update_uses_actual_groups,addM_read,product64_value,List.sum_cons,add_assoc]

noncomputable def runProbe (F : Frame f pₜ) (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell)
    (child : M→Fin 64→Meter (Block F ell)) : Meter (Block F ell) :=
  let m := startingCursor I hq
  let u := zeroM (ell:=ell) (f:=F.words) F.hp
  match m.result with
  | none => ⟨u.result,u.steps+m.steps⟩
  | some P =>
    let out := modeDrain (modeUpdate F I hv child) P u.result (u.steps+m.steps)
    ⟨out.result.1,out.steps⟩

theorem streamed_probe_replaces_list (hf : f.Monic) (F : Frame f pₜ)
    (I : SiteTape sel d t q) (hq : 0<q) (hv : 0<ell) (child : M→Fin 64→Meter (Block F ell))
    (prior : List M) (hn : prior.Nodup) (hall : ∀ b,b∈prior) :
    (runProbe F I hq hv child).result=(groupedProbe F.hp F.sizePos hv prior child).result := by
  letI := nativeMenuFinite (shape S Δ sel) c t
  let init := zeroM (ell:=ell) (f:=F.words) F.hp
  let prep := startingCursor I hq
  obtain ⟨P,hP,_,hRun⟩ := starting_cursor_exact I hq
  let out := modeDrain (modeUpdate F I hv child) P init.result (init.steps+prep.steps)
  obtain ⟨v,_⟩ := halt_driven_fold_exact P (tupleSpec I) hRun (modeUpdate F I hv child)
    init.result (init.steps+prep.steps)
  obtain ⟨order,hO,hAll,hE⟩ := native_mode_order sel d t I
  apply frame_words_injective hf F
  unfold Frame.decode
  congr 1
  rw [runProbe,hP]
  change uvRead F.hp F.words ell out.result.1=_
  have e : out.result.1=(foldExpected (modeUpdate F I hv child) (tupleSpec I) init.result).result :=
    congrArg Prod.fst v
  rw [e,show tupleSpec I=order.map (vectorKey sel d t I) from hE.symm,fold_typed_mode_output]
  rw [show uvRead F.hp F.words ell init.result=0 from zeroM_read F.hp,zero_add,
    grouped_probe_value,complete_sum order hO hAll,complete_sum prior hn hall]

#print axioms weighted_component_le
#print axioms actual_legal_coordinates_fit
#print axioms mode_update_uses_actual_groups
#print axioms fold_typed_mode_output
#print axioms streamed_probe_replaces_list
end J6R49DFS
