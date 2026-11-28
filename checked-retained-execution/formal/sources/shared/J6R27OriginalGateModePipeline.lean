
import J6R27OriginalGateMaskBank
import J6R27OriginalGateSourceSupport
import J6R27OriginalGateModeMeaning

/-! One generated packet's complete ModeInput list is run from its
R17 sparse emitted support, the actual resident mode roster and one
resident chosen page-mask file. A typed output list and its native
ModeMeaning are conclusions, not runtime inputs. -/
namespace J6R27OriginalGate
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R18ChildWrite P11FullPacking
open AOracleMachineTimeTape J6R16ModeCost J6R10Repack

def compileModes {a q b : ℕ} (i : Fin a) (p : ℕ) (fit : i.val+1≤q)
    (axis : List Bool) (owner : PageRef q) (g : Word 6) (start : Word b)
    (raw : List (RawMode q)) (terms : List (RawMode q×Word q)) (maskBank : List (MaskRow q)) :
    Meter (Option (List (ModeInput a p i q))) :=
  let d := densify raw terms
  match d.result with
  | none => ⟨none,d.steps+4⟩
  | some es =>
    let c := bindModeMasks a axis maskBank raw es
    match c.result with
    | none => ⟨none,d.steps+c.steps+8⟩
    | some input =>
      let result := writeModeRoster i p fit axis owner g start input
      ⟨result.result,d.steps+c.steps+result.steps+8⟩

def pipelineFee (a i q b roster pages : ℕ) : ℕ :=
  22+roster*(denseRecordFee a q+modeBindingFee a q pages+
    buildModeInputCap a i q b+13*b+12)

set_option maxHeartbeats 4700000 in
theorem compile_modes_exact {a pages p q b : ℕ} (i : Fin a)
    (qFit : i.val+1≤q) (pageFit : pages≤2^q) (pFit : p<2^q)
    (axis : List Bool) (clock : axis.length=i.val)
    (mask : MaskFamily a pages (Fin 64)) (k : Page a pages (Fin 64)) (g : Fin 64)
    (rank : Word b) (bPos : 0<b) (xs : List (TypedModePair i pages p q))
    (rankFit : rank.val+xs.length<2^b)
    (raw : List (RawMode q)) (rawMeaning : raw=xs.map (fun x=>encodeMode i x.1))
    (rawDistinct : raw.Nodup)
    (terms : List (RawMode q×Word q)) (emitted : terms=supportSpec raw (xs.map Prod.snd))
    (pageList : List (Page a pages (Fin 64))) (cover : ∀ j,j∈pageList)
    (bank : List (MaskRow q)) (maskMeaning : bank=pageList.map (encodeMaskRow mask)) :
    let z := compileModes i p qFit axis (pageRef q k) (word g.val) rank raw terms bank
    ∃ ys, z.result=some ys ∧ ModeRosterSpec i b mask k g rank.val xs ys ∧
      z.steps≤pipelineFee a i.val q b xs.length pageList.length := by
  subst bank
  subst terms
  let d := densify raw (supportSpec raw (xs.map Prod.snd))
  have L : raw.length=(xs.map Prod.snd).length := by rw [rawMeaning,List.length_map,List.length_map]
  have gD : d.result=some (xs.map Prod.snd) := actual_sparse_to_dense raw _ L rawDistinct
  have H : ∀ m∈raw,m.key.1.length≤6*a ∧ m.key.2.length≤6*a := by
    intro m h
    rw [rawMeaning] at h
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp h
    obtain ⟨h1,h2⟩ := source_key_widths i x.1 (q:=q)
    exact ⟨h1.le,h2.le⟩
  have dFee : d.steps≤4+raw.length*denseRecordFee a q := densify_cost a raw _ H
  let c := bindModeMasks a axis (pageList.map (encodeMaskRow mask)) raw (xs.map Prod.snd)
  have hC : c.result=some (xs.map (encodeCandidate i mask)) ∧
      c.steps≤5+xs.length*modeBindingFee a q pageList.length := by
    simpa only [c,rawMeaning] using bind_source_mask_tape pageFit i axis clock mask pageList cover xs
  let w := writeModeRoster i p qFit axis (pageRef q k) (word g.val) rank (xs.map (encodeCandidate i mask))
  obtain ⟨ys,hY,spec,hW⟩ := write_native_roster i qFit pageFit pFit axis clock mask k g rank bPos
    xs rankFit _ rfl
  have norm :
      compileModes i p qFit axis (pageRef q k) (word g.val) rank raw
        (supportSpec raw (xs.map Prod.snd)) (pageList.map (encodeMaskRow mask))=
          ⟨w.result,d.steps+c.steps+w.steps+8⟩ := by
    unfold compileModes
    dsimp only
    rw [gD]
    dsimp only
    rw [hC.1]
  rw [norm]
  refine ⟨ys,hY,spec,?_⟩
  change d.steps+c.steps+w.steps+8≤_
  change w.steps≤_ at hW
  have h := hC.2
  rw [rawMeaning,List.length_map] at dFee
  unfold pipelineFee
  simp only [Nat.mul_add] at hW ⊢
  omega

variable {E A B : Type} {N : Network E A B}

set_option maxHeartbeats 2000000 in
theorem compiled_native_roster_meaning {a p q b n : ℕ} (i : Fin a)
    (P : PhysicalPacking N a (Fin 64)) (page : Page a P.copies (Fin 64)) (g : Fin 64)
    (ξ : Fin n≃PacketMode i P.copies (2^(i.val+1)) p)
    (β : J6R9PacketScopes.Mode i p P.mask→₀ℕ) (es : Fin n→Word q)
    (literal : ∀ j,(es j).val=β ((packet_mode_equiv P.mask i p).symm (ξ j)))
    (ys : List (ModeInput a p i q))
    (verified : ModeRosterSpec i b P.mask page g 1 (List.ofFn (fun j=>(ξ j,es j))) ys) :
    ∃ ms, List.ofFn ms=ys ∧
      ModeMeaning P i g page (ξ.trans (packet_mode_equiv P.mask i p).symm) β ms ∧
      ∀ j,(ms j).code=encodeBits b j.succ.val :=
  meaning_of_emitted_roster P i g page ξ es β literal ys verified

#print axioms compile_modes_exact
end J6R27OriginalGate


