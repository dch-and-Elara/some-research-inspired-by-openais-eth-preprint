import J6R17ModeTapeDispatch
import J6R17ModeTapeSite

/-! The actual enumerator reads the produced tape. On each emit pulse
its vector can immediately be dispatched in matching address order.
The list of pulses is a proof transcript, not required live storage. -/
namespace J6R17ModeTape
open scoped Classical Polynomial
open AOracleMachineTime J6R12CollisionEdges
open J6R15ModeCost J6R16ModeCost J6R12Blueprint J6ActiveRun J6R11Blueprint J6R10Reachable

def dispatchStream {q : ℕ} (a : ℕ) (T : RawTape q) (vectors : List (List (Word q))) :
    Meter (List (Option (List (RawMode q×Word q)))) :=
  mapMeter (emitSupport a T.modes) vectors

theorem dispatchStream_exact {q : ℕ} (a : ℕ) (T : RawTape q) (vectors : List (List (Word q)))
    (hL : ∀ es∈vectors,es.length=T.modes.length) :
    let z := dispatchStream a T vectors
    z.result=vectors.map (fun es=>some (supportSpec T.modes es)) ∧
      z.steps≤(T.modes.length*dispatchStride a q+10)*vectors.length := by
  exact mapMeter_exact _ _ _ vectors (fun v hv=> by
    obtain ⟨hs,hC⟩ := emitSupport_exact a T.modes v (hL v hv).symm
    exact ⟨hs,hC.le⟩)

theorem run_ready_raw {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)}
    {Δ q : ℕ} (hq : 0<q) (sel : Selector S Δ) {c : Call (PhysicalHost f ell)}
    (d : Ready S Δ c) (t : Center S c) (I : SiteTape sel d t q) (T : RawTape q)
    (hm : T.modes=I.modes.map (encodeMode (centerIndex d t))) (hw : T.weights=I.words)
    (hp : T.precision=I.precision) :
    let a := S.levelBits c.depth
    let xs := strictTuples (I.modes.map modeWeight) (registerPrecision S c t)
    ∃ st,
      (start T.weights T.precision).result=.again st ∧
      let run := collect T.weights.length (xs.length+1) st
      run.result.2=true ∧ run.result.1.map (List.map Word.val)=xs ∧
      (∀ es∈run.result.1,∃! β : NativeMenu (shape S Δ sel) c t,
        I.modes.map (fun m=>β.val ((site_mode_equiv sel d t).symm m))=es.map Word.val) ∧
      let dispatch := dispatchStream a T run.result.1
      dispatch.result=run.result.1.map (fun es=>some (supportSpec T.modes es)) ∧
      dispatch.steps≤(T.modes.length*dispatchStride a q+10)*xs.length := by
  let a := S.levelBits c.depth
  let p := registerPrecision S c t
  let xs := strictTuples (I.modes.map modeWeight) p
  obtain ⟨st,hStart,_,hDone,hOut,_⟩ :=
    roster_paid hq (register_positive d t) I.modes I.words I.precision I.weightMeaning I.precisionMeaning
  have hS : (start T.weights T.precision).result=.again st := by rwa [hw,hp]
  let u := collect T.weights.length (xs.length+1) st
  have hU : u.result.1.map (List.map Word.val)=xs := by
    unfold u
    rwa [hw]
  have hH : u.result.2=true := by unfold u; rwa [hw]
  have hM (es : List (Word q)) (he : es∈u.result.1) : es.map Word.val∈xs := by
    rw [← hU]
    exact List.mem_map.mpr ⟨es,he,rfl⟩
  have hPos (w : ℕ) (he : w∈I.modes.map modeWeight) : 0<w := by
    obtain ⟨m,_,rfl⟩ := List.mem_map.mp he
    exact (modeWeight_bounds m).1
  have hTuple := (strictTuples_exact (I.modes.map modeWeight) p hPos).2
  have hL (es : List (Word q)) (he : es∈u.result.1) : es.length=T.modes.length := by
    have h := ((hTuple _).mp (hM es he)).1
    rw [List.length_map,List.length_map] at h
    rwa [hm,List.length_map]
  have hLen : u.result.1.length=xs.length := by
    have H := congrArg List.length hU
    rwa [List.length_map] at H
  have hd := dispatchStream_exact a T u.result.1 hL
  exact ⟨st,hS,hH,hU,fun es he=>(native_tuple_iff sel d t I.modes I.nodup I.allModes _).mp (hM es he),
    hd.1,by simpa only [hLen] using hd.2⟩

#print axioms dispatchStream_exact
#print axioms run_ready_raw
end J6R17ModeTape

