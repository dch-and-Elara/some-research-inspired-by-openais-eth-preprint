import J6R51DispatchCore
import J6R17ModeTapeCodec

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000

/-! Literal raw modes distinguish orientation words, copy, tile and
weight. The map of hidden variables exists only in the proof; runtime
compares the actual stored raw keys. -/
namespace J6R51Dispatch
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R14LayoutCost

theorem injective_encoder_replays_word_permutation {X : Type*} {q : ℕ}
    (encode : X  →  RawMode q) (inject : Function.Injective encode) (values : X  →  Word q)
    (source target : List X) (cover : ∀ x∈target,x∈source) :
    (replayDense (supportSpec (source.map encode) (source.map values))
      (target.map encode)).result=target.map values := by
  classical
  let value : RawMode q  →  Word q := fun z=>if h : ∃ x,encode x=z then values (Classical.choose h) else word 0
  have defined (x : X) : value (encode x)=values x := by
    have h : ∃ z,encode z=encode x := ⟨x,rfl⟩
    unfold value
    rw [dif_pos h]
    exact congrArg values (inject (Classical.choose_spec h))
  have sourceWords : (source.map encode).map value=source.map values := by
    rw [List.map_map]
    exact List.map_congr_left (fun x _=>defined x)
  have targetWords : (target.map encode).map value=target.map values := by
    rw [List.map_map]
    exact List.map_congr_left (fun x _=>defined x)
  have seen (j : RawMode q) (hm : j∈target.map encode) : j∈source.map encode := by
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
    exact List.mem_map_of_mem (f:=encode) (cover x hx)
  have out := replay_across_literal_rosters (source.map encode) (target.map encode) value seen
  rwa [sourceWords,targetWords] at out

theorem true_packet_mode_key_charge {a q pages tiles p : ℕ} (i : Fin a)
    (m : PacketMode i pages tiles p) :
    compareCharge (encodeMode (q:=q) i m)=60*a+30*q+35 := by
  unfold compareCharge encodeMode wordCell
  simp only [coordinateLabel_len]
  omega

theorem true_packet_modes_replay {a q pages tiles p : ℕ} (i : Fin a)
    (pagesFit : pages<2^q) (tilesFit : tiles<2^q) (precisionFit : p<2^q)
    (source target : List (PacketMode i pages tiles p)) (cover : ∀ x∈target,x∈source)
    (values : PacketMode i pages tiles p → Word q) :
    let sp := supportSpec (source.map (encodeMode i)) (source.map values)
    let out := replayDense sp (target.map (encodeMode i))
    out.result=target.map values ∧
      out.steps ≤ 2+target.length*(3*q+7+sp.length*(60*a+30*q+35)) := by
  have r := injective_encoder_replays_word_permutation (encodeMode i)
    (encodeMode_inj i pagesFit tilesFit precisionFit) values source target cover
  have f := replay_actual_scan_fee (supportSpec (source.map (encodeMode i)) (source.map values))
    (target.map (encodeMode i)) (60*a+30*q+35) (by
      intro k hk
      obtain ⟨m,_,rfl⟩ := List.mem_map.mp hk
      exact (true_packet_mode_key_charge (q:=q) i m).le)
  simpa only [List.length_map] using And.intro r f

#print axioms injective_encoder_replays_word_permutation
#print axioms true_packet_mode_key_charge
#print axioms true_packet_modes_replay
end J6R51Dispatch

