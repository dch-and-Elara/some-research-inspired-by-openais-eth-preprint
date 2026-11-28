import J6R68RateJointRootWordsCopy

/-! Copy exactly the already selected active resident replay fields in their
original order. The unexecuted packed proof/chart metadata is retained by
reference; the copied seats, page masks and mode/weight roster are the
fields read by the actual numerical occurrence compiler. -/
namespace J6R68RateJoint.RootWords
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R53OldOwner J6R14LayoutCost J6R17ModeTape J6R50SourceProducer
open J6R32ChildResidentTransfer J6R33GeneratedChildSite P11FullPacking

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3400
set_option maxHeartbeats 14000000
set_option Elab.async false
noncomputable section

def copyModeFields {q : ℕ} (x : RawMode q) : Meter (RawMode q) :=
  let l := copyBytes x.key.1
  let r := copyBytes x.key.2
  let p := copyFixed x.page
  let t := copyFixed x.tile
  let w := copyFixed x.weight
  ⟨⟨(l.result,r.result),p.result,t.result,w.result⟩,l.steps+r.steps+p.steps+t.steps+w.steps+7⟩

def modeCopyFee {q : ℕ} (x : RawMode q) : ℕ := 3*(x.key.1.length+x.key.2.length)+9*q+12

theorem copy_mode_fields_exact {q : ℕ} (x : RawMode q) :
    copyModeFields x=⟨x,modeCopyFee x⟩ := by
  rcases x with ⟨⟨l,r⟩,p,t,w⟩
  simp only [copyModeFields,copyBytes_exact,copy_fixed_exact,modeCopyFee]
  congr 1
  omega

def copyModeFieldsTape {q : ℕ} : List (RawMode q)→Meter (List (RawMode q))
  | [] => ⟨[],3⟩
  | x::xs =>
    let h := copyModeFields x
    let t := copyModeFieldsTape xs
    ⟨h.result::t.result,h.steps+t.steps+4⟩

theorem copy_mode_fields_tape_exact {q : ℕ} (xs : List (RawMode q)) :
    copyModeFieldsTape xs=⟨xs,3+(xs.map (fun x=>modeCopyFee x+4)).sum⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [copyModeFieldsTape,copy_mode_fields_exact,ih,List.map_cons,List.sum_cons]
    congr 1
    omega

def copyResidentFields {a q : ℕ} (x : ChildResidents a q) : Meter (ChildResidents a q) :=
  let c := copyFixed x.raw.copies
  let m := copyMaskTape x.raw.masks
  let k := copyModeFieldsTape x.raw.roster.modes
  let w := copyGateKeys x.raw.roster.weights
  let p := copyFixed x.raw.roster.precision
  let s := copySeatTape x.seats
  ⟨⟨⟨x.raw.packed,c.result,m.result,⟨k.result,w.result,p.result⟩⟩,s.result⟩,
    c.steps+m.steps+k.steps+w.steps+p.steps+s.steps+9⟩

def residentFieldsFee (a q n masks modes weights : ℕ) : ℕ :=
  2*(3*(q+1)+1)+21+masks+modes+(3*(q+1)+5)*weights+
    (3*(a+((q-a)+13*a))+51)*n

theorem copy_resident_fields_exact {a q : ℕ} (x : ChildResidents a q) :
    copyResidentFields x=⟨x,
      residentFieldsFee a q x.seats.length
        (x.raw.masks.map (fun h=>copiedMaskFee h+5)).sum
        (x.raw.roster.modes.map (fun h=>modeCopyFee h+4)).sum
        x.raw.roster.weights.length⟩ := by
  rcases x with ⟨⟨packed,cp,ms,ks,ws,p⟩,s⟩
  simp only [copyResidentFields,copy_fixed_exact,copy_mask_tape_exact,copy_mode_fields_tape_exact,
    copy_gate_keys_exact,copy_seat_tape_exact,residentFieldsFee]
  congr 1
  omega

private theorem constant_charge_sum {A : Type*} (f : A→ℕ) (xs : List A) (k : ℕ)
    (h : ∀ x∈xs,f x=k) : (xs.map f).sum=k*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have e := h x List.mem_cons_self
    have b := ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.sum_cons,e,b,List.length_cons,Nat.mul_succ]
    omega

private theorem mask_stride {a b q : ℕ} (F : MaskFamily a b (Fin 64)) (k : Page a b (Fin 64)) :
    copiedMaskFee (encodeMaskRow (q:=q) F k)+5=39*a+3*q+18 := by
  unfold copiedMaskFee
  simp only [encodeMaskRow,pageRef,wordCell,coordinateLabel_len,List.length_ofFn]
  omega

private theorem mode_stride {a b t p q : ℕ} (i : Fin a) (m : PacketMode i b t p) :
    modeCopyFee (encodeMode (q:=q) i m)+4=36*a+9*q+16 := by
  unfold modeCopyFee
  simp only [encodeMode,wordCell,coordinateLabel_len]
  omega

def chartResidentFee (a q edges copies modes : ℕ) : ℕ :=
  residentFieldsFee a q edges
    ((39*a+3*(q+1)+18)*((2^(6*a)*2^(6*a))*copies))
    ((36*a+9*(q+1)+16)*modes) modes

theorem copy_resident_fields_from_exact_geometry
    {E A B : Type} {N : J6R10Repack.Network E A B} {a q p : ℕ}
    {P : J6R10Repack.PhysicalPacking N a (Fin 64)} {i : Fin a}
    {R : ChildResidents a q} (H : ResidentReceipt P i p R) :
    copyResidentFields R=⟨R,chartResidentFee a q H.edges.length P.copies H.modes.length⟩ := by
  have s : R.seats.length=H.edges.length := by rw [H.seats,List.length_map]
  have w : R.raw.roster.weights.length=H.modes.length := by
    have e := congrArg List.length H.weights
    simpa only [List.length_map] using e
  have m : (R.raw.masks.map (fun x=>copiedMaskFee x+5)).sum=
      (39*a+3*(q+1)+18)*((2^(6*a)*2^(6*a))*P.copies) := by
    have z := constant_charge_sum (fun x=>copiedMaskFee x+5) R.raw.masks (39*a+3*(q+1)+18)
      (fun x hx=>by
        rw [H.masks] at hx
        obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
        exact mask_stride P.mask k)
    have len : R.raw.masks.length=(2^(6*a)*2^(6*a))*P.copies := by
      rw [H.masks,List.length_map,(child_pages_complete a P.copies).2.2]
    rwa [len] at z
  have t : (R.raw.roster.modes.map (fun x=>modeCopyFee x+4)).sum=
      (36*a+9*(q+1)+16)*H.modes.length := by
    have z := constant_charge_sum (fun x=>modeCopyFee x+4) R.raw.roster.modes (36*a+9*(q+1)+16)
      (fun x hx=>by
        rw [H.rawModes] at hx
        obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
        exact mode_stride i k)
    rwa [raw_roster_clock H] at z
  rw [copy_resident_fields_exact,s,m,t,w]
  rfl

#print axioms copy_mode_fields_exact
#print axioms copy_mode_fields_tape_exact
#print axioms copy_resident_fields_exact
#print axioms copy_resident_fields_from_exact_geometry
end
end J6R68RateJoint.RootWords

