
import J6R27OriginalGateModeInput

/-! Produce an entire ordered ModeInput stream, not just the active
multiplicities. Legacy IDs are issued by a real ripple counter starting
at its resident initial word. Legal descriptors produce no failure;
misaligned/invalid entry words need not be assigned semantics. -/
namespace J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R17ModeTape
open J6R18ChildWrite P11FullPacking J6R9PacketScopes

structure ModeCandidate (q : ℕ) where
  raw : RawMode q
  maskBit : Bool
  exponent : Word q

def writeModeRoster {a q b : ℕ} (i : Fin a) (p : ℕ) (fit : i.val+1≤q)
    (axis : List Bool) (owner : PageRef q) (g : Word 6) :
    Word b→List (ModeCandidate q)→Meter (Option (List (ModeInput a p i q)))
  | _,[] => ⟨some [],5⟩
  | rank,x::xs =>
    let u := buildModeInput i p fit axis x.raw owner g x.maskBit rank x.exponent
    let next := increment rank
    let v := writeModeRoster i p fit axis owner g next.result xs
    ⟨u.result.bind (fun y=>v.result.map (y::·)),u.steps+v.steps+next.steps+8⟩

abbrev TypedModePair {a : ℕ} (i : Fin a) (pages p q : ℕ) :=
  PacketMode i pages (2^(i.val+1)) p × Word q

noncomputable def encodeCandidate {a pages p q : ℕ} (i : Fin a)
    (mask : MaskFamily a pages (Fin 64)) (x : TypedModePair i pages p q) :
    ModeCandidate q :=
  ⟨encodeMode i x.1,selectedMaskBit mask x.1.1.val i,x.2⟩

structure ModeAtSpec {a pages p q : ℕ} (i : Fin a) (b : ℕ)
    (mask : MaskFamily a pages (Fin 64)) (page : Page a pages (Fin 64)) (g : Fin 64)
    (rank : ℕ) (x : TypedModePair i pages p q) (y : ModeInput a p i q) : Prop where
  code : y.code=encodeBits b rank
  tile : y.tile.val=x.1.2.1.val
  order : y.order=x.1.2.2
  exponent : y.beta=x.2
  target : y.targeted=true ↔ x.1.1.val=page ∧
    rowGroup mask i (x.1.1.val,tileIndex i x.1.2.1)=g
  source : y.sourced=true ↔ x.1.1.val=page ∧
    colGroup mask i (x.1.1.val,tileIndex i x.1.2.1)=g

inductive ModeRosterSpec {a pages p q : ℕ} (i : Fin a) (b : ℕ)
    (mask : MaskFamily a pages (Fin 64)) (page : Page a pages (Fin 64)) (g : Fin 64) :
    ℕ→List (TypedModePair i pages p q)→List (ModeInput a p i q)→Prop
  | nil {rank} : ModeRosterSpec i b mask page g rank [] []
  | cons {rank x xs y ys} :
    ModeAtSpec i b mask page g rank x y →
    ModeRosterSpec i b mask page g (rank+1) xs ys →
    ModeRosterSpec i b mask page g rank (x::xs) (y::ys)

theorem mode_roster_length {a pages p q b rank : ℕ} {i : Fin a}
    {mask : MaskFamily a pages (Fin 64)} {page : Page a pages (Fin 64)} {g : Fin 64}
    {xs : List (TypedModePair i pages p q)} {ys : List (ModeInput a p i q)}
    (h : ModeRosterSpec i b mask page g rank xs ys) : ys.length=xs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons,ih]

theorem mode_roster_at {a pages p q b rank : ℕ} {i : Fin a}
    {mask : MaskFamily a pages (Fin 64)} {page : Page a pages (Fin 64)} {g : Fin 64}
    {xs : List (TypedModePair i pages p q)} {ys : List (ModeInput a p i q)}
    (h : ModeRosterSpec i b mask page g rank xs ys) (j : ℕ)
    (ha : j<xs.length) (hb : j<ys.length) :
    ModeAtSpec i b mask page g (rank+j) xs[j] ys[j] := by
  induction h generalizing j with
  | nil => simp at ha
  | cons head _ ih =>
    cases j with
    | zero => simpa only [Nat.add_zero,List.getElem_cons_zero] using head
    | succ j =>
      have K := ih j (Nat.lt_of_succ_lt_succ ha) (Nat.lt_of_succ_lt_succ hb)
      simp only [List.getElem_cons_succ]
      have H (v : ℕ) : v+j.succ=(v+1)+j := by omega
      rw [H]
      exact K

set_option maxHeartbeats 3900000 in
theorem write_native_roster {a pages p q b : ℕ} (i : Fin a)
    (hq : i.val+1≤q) (hPage : pages≤2^q) (hp : p<2^q)
    (axis : List Bool) (clock : axis.length=i.val)
    (mask : MaskFamily a pages (Fin 64)) (page : Page a pages (Fin 64)) (g : Fin 64)
    (rank : Word b) (hb : 0<b) (xs : List (TypedModePair i pages p q))
    (rankFit : rank.val+xs.length<2^b)
    (resident : List (ModeCandidate q)) (valid : resident=xs.map (encodeCandidate i mask)) :
    let z := writeModeRoster i p hq axis (pageRef q page) (word g.val) rank resident
    ∃ ys, z.result=some ys ∧ ModeRosterSpec i b mask page g rank.val xs ys ∧
      z.steps≤5+xs.length*(buildModeInputCap a i.val q b+13*b+12) := by
  subst resident
  induction xs generalizing rank with
  | nil =>
    refine ⟨[],rfl,.nil,?_⟩
    simp only [List.map_nil,writeModeRoster,List.length_nil,Nat.zero_mul,Nat.add_zero,le_refl]
  | cons x xs ih =>
    let u := buildModeInput i p hq axis (encodeMode (q:=q) i x.1) (pageRef q page)
      (word g.val) (selectedMaskBit mask x.1.1.val i) rank x.2
    let next := increment rank
    obtain ⟨m,received,code,tile,order,exponent,target,source,cost⟩ :=
      actual_mode_input i hq hPage hp axis clock mask x.1 page g rank x.2
    have e1 : rank.val+1<2^b := by simp only [List.length_cons] at rankFit; omega
    obtain ⟨nv,nc⟩ := increment_exact hb rank e1
    have f : next.result.val+xs.length<2^b := by
      change next.result.val=_ at nv
      rw [nv]
      simp only [List.length_cons] at rankFit
      omega
    obtain ⟨ys,hy,spec,fee⟩ := ih next.result f
    have codeE : m.code=encodeBits b rank.val := by
      rw [code,show encodeBits b rank.val=(word (q:=b) rank.val).bits from rfl,valued_word rank]
    have head : ModeAtSpec i b mask page g rank.val x m := ⟨codeE,tile,order,exponent,target,source⟩
    rw [nv] at spec
    refine ⟨m::ys,?_,.cons head spec,?_⟩
    · change u.result.bind (fun m=>
        (writeModeRoster i p hq axis (pageRef q page) (word g.val) next.result
          (xs.map (encodeCandidate i mask))).result.map (m::·))=_
      change u.result=some m at received
      rw [received,hy]
      rfl
    · change u.steps+(writeModeRoster i p hq axis (pageRef q page) (word g.val)
        next.result (xs.map (encodeCandidate i mask))).steps+next.steps+8≤_
      change u.steps≤_ at cost
      change next.steps=_ at nc
      rw [nc,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

#print axioms mode_roster_length
#print axioms mode_roster_at
#print axioms write_native_roster
end J6R27OriginalGate



