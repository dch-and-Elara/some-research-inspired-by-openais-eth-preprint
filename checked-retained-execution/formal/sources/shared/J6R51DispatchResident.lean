import J6R51DispatchCodec
import J6R51DispatchModeIdentity
import J6R33GeneratedChildSiteSparse

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12500000
set_option maxRecDepth 2400

/-! A real R49 source mode tape can have a different roster order srcModes
the selected installed R33/R50 resident chart. The emitted sparse bytes,
not an abstract tuple callback, are reindexed at their shared width. -/
namespace J6R51Dispatch
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R32ChildResidentTransfer J6R33GeneratedChildSite

variable {q : ℕ}

def emitAndReplay (a : ℕ) (source target : List (RawMode q)) (dense : List (Word q)) :
    Meter (Option (List (Word q))) :=
  let first := emitSupport a source dense
  match first.result with
  | none => ⟨none,first.steps+3⟩
  | some sp =>
    let out := replayDense sp target
    ⟨some out.result,first.steps+out.steps+3⟩

theorem emit_and_replay_measured (a : ℕ) (source target : List (RawMode q)) (dense : List (Word q))
    (len : source.length=dense.length) :
    let out := emitAndReplay a source target dense
    let sp := supportSpec source dense
    let R := replayDense sp target
    out.result=some R.result ∧ out.steps=source.length*dispatchStride a q+4+R.steps+3 := by
  obtain ⟨r,f⟩ := emitSupport_exact a source dense len
  unfold emitAndReplay
  dsimp only
  rw [r]
  dsimp only
  rw [f]
  exact ⟨rfl,rfl⟩

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}

theorem actual_resident_exponents_replayed
    (d : Ready S Δ c) (w : NativeAddress (shape S Δ sel) c)
    (I : SiteTape sel d w.1 (q+1)) {R : ChildResidents (S.levelBits c.depth) q}
    (H : ResidentReceipt (packing sel d) (centerIndex d w.1) (registerPrecision S c w.1) R)
    (srcModes : List (RawMode (q+1)))
    (fromExact : srcModes = I.modes.map (encodeMode (centerIndex d w.1)))
    (dense : List (Word (q+1)))
    (actual : dense.map Word.val=vectorKey sel d w.1 I w.2.2.1)
    (pageRoom : (packing sel d).copies<2^(q+1))
    (tileRoom : 2^((centerIndex d w.1).val+1)<2^(q+1)) :
    let a := S.levelBits c.depth
    let out := emitAndReplay a srcModes R.raw.roster.modes dense
    let sp := supportSpec srcModes dense
    ∃ ready : List (Word (q+1)),out.result=some ready ∧
      ready.map Word.val=H.modes.map
        (fun m=>siteTuple sel d w ((packet_mode_equiv (packing sel d).mask
          (centerIndex d w.1) (registerPrecision S c w.1)).symm m)) ∧
      out.steps ≤ srcModes.length*dispatchStride a (q+1)+4+
        (2+H.modes.length*(3*(q+1)+7+sp.length*(60*a+30*(q+1)+35)))+3 := by
  let i := centerIndex d w.1
  let p := registerPrecision S c w.1
  let code := fun m : NativeRoster sel d w.1=>w.2.2.1.val ((site_mode_equiv sel d w.1).symm m)
  let bytes := fun m=>word (q:=q+1) (code m)
  have denseSpec : dense=I.modes.map bytes := by
    have h := congrArg (List.map (word (q:=q+1))) actual
    unfold vectorKey at h
    rw [List.map_map,List.map_map] at h
    have norm : dense.map ((word (q:=q+1)) ∘ Word.val)=dense :=
      (List.map_congr_left (fun x (_ : x∈dense)=>valued_word x)).trans (List.map_id _)
    exact norm.symm.trans h
  have plen : p<2^(q+1) := by
    unfold p
    rw [←I.precisionMeaning]
    exact val_lt I.precision
  have hd : srcModes.length=dense.length := by rw [fromExact,denseSpec,List.length_map,List.length_map]
  have support := emit_and_replay_measured (S.levelBits c.depth) srcModes R.raw.roster.modes dense hd
  have br := true_packet_modes_replay i pageRoom tileRoom plen I.modes H.modes
    (fun m _=>I.allModes m) bytes
  let D := replayDense (supportSpec srcModes dense) R.raw.roster.modes
  have eq : D.result=H.modes.map bytes := by
    unfold D
    rw [fromExact,H.rawModes,denseSpec]
    exact br.1
  have fee : D.steps ≤ 2+H.modes.length*(3*(q+1)+7+(supportSpec srcModes dense).length*
      (60*S.levelBits c.depth+30*(q+1)+35)) := by
    unfold D
    rw [fromExact,H.rawModes,denseSpec]
    exact br.2
  refine ⟨D.result,support.1,?_,?_⟩
  · rw [eq,List.map_map]
    apply List.map_congr_left
    intro m _
    have hM : code m<2^(q+1) := by
      have inVals : code m∈dense.map Word.val := by
        rw [actual]
        change code m∈I.modes.map code
        exact List.mem_map_of_mem (f:=code) (I.allModes m)
      obtain ⟨entry,_,hE⟩ := List.mem_map.mp inVals
      rw [←hE]
      exact val_lt entry
    exact (word_val hM).trans (true_site_tuple_reads_encoded_variable d w m).symm
  · rw [support.2]
    exact Nat.add_le_add_right (Nat.add_le_add_left fee _) _

#print axioms emit_and_replay_measured
#print axioms actual_resident_exponents_replayed
end J6R51Dispatch

