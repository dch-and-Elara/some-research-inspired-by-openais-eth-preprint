
import J6R27OriginalGateModeRoster
import J6R16ModeCostCatalog

/-! Forget only serialization, not any information: every record in
the completely emitted typed list is a correctly addressed native
mode. The exponent premise is the semantic match to the selected
R17/R25 actual emitted tuple, not a condition on the output list. -/
namespace J6R27OriginalGate
open P11FullPacking J6R10Repack J6R9PacketScopes J6R18ChildWrite J6R16ModeCost
open J6R17ModeTape J6R15ModeCost AOracleMachineTimeTape

variable {E A B : Type}
variable {N : Network E A B} {a p q b m : ℕ}

set_option maxHeartbeats 3400000 in
theorem meaning_of_emitted_roster (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (g : Fin 64) (k : Page a P.copies (Fin 64))
    (ξ : Fin m≃PacketMode i P.copies (2^(i.val+1)) p)
    (exponents : Fin m→Word q) (β : J6R9PacketScopes.Mode i p P.mask→₀ℕ)
    (hBeta : ∀ j,(exponents j).val=β ((packet_mode_equiv P.mask i p).symm (ξ j)))
    (ys : List (ModeInput a p i q))
    (H : ModeRosterSpec i b P.mask k g 1 (List.ofFn (fun j=>(ξ j,exponents j))) ys) :
    ∃ ms : Fin m→ModeInput a p i q,
      List.ofFn ms=ys ∧ ModeMeaning P i g k (ξ.trans (packet_mode_equiv P.mask i p).symm) β ms ∧
      ∀ j,(ms j).code=encodeBits b j.succ.val := by
  let xs := List.ofFn (fun j=>(ξ j,exponents j))
  have len : ys.length=m := (mode_roster_length H).trans (List.length_ofFn)
  let ms : Fin m→ModeInput a p i q := fun j=>getElem ys j.val (len.symm ▸ j.isLt)
  have J (j : Fin m) : ModeAtSpec i b P.mask k g (1+j.val) (ξ j,exponents j) (ms j) := by
    have h1 : j.val<xs.length := by rw [List.length_ofFn]; exact j.isLt
    have h2 : j.val<ys.length := len.symm ▸ j.isLt
    have I := mode_roster_at H j.val h1 h2
    change ModeAtSpec i b P.mask k g (1+j.val) xs[j.val] (ms j) at I
    rw [List.getElem_ofFn] at I
    exact I
  refine ⟨ms,?_,?_,?_⟩
  · apply List.ext_getElem (by rw [List.length_ofFn,len])
    intro j hj hy
    rw [List.getElem_ofFn]
  · refine {
      tile := fun j=>(J j).tile
      order := fun j=>(J j).order
      exponents := fun j=>by simp only [(J j).exponent,hBeta,Equiv.trans_apply]
      target := ?_
      source := ?_ }
    · intro j
      let m := ξ j
      change (ms j).targeted=true ↔ (rowGroup P.mask i (m.1.val,tileIndex i m.2.1),m.1.val)=(g,k)
      exact (J j).target.trans ⟨fun h=>Prod.ext h.2 h.1,
        fun h=>⟨congrArg Prod.snd h,congrArg Prod.fst h⟩⟩
    · intro j
      let m := ξ j
      change (ms j).sourced=true ↔ (colGroup P.mask i (m.1.val,tileIndex i m.2.1),m.1.val)=(g,k)
      exact (J j).source.trans ⟨fun h=>Prod.ext h.2 h.1,
        fun h=>⟨congrArg Prod.snd h,congrArg Prod.fst h⟩⟩
  · intro j
    simpa only [Fin.val_succ,Nat.add_comm] using (J j).code

#print axioms meaning_of_emitted_roster
end J6R27OriginalGate




