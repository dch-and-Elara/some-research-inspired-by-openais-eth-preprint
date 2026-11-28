
import J6R30GeneratedRootLayoutTags

/-! Attach original signed Plant endpoints to the generated stable
root records. The compact *input* is the original finite port file,
not a padded table or a completed assignment truth table. Lookup uses
the actual binary wire ordinal and a charged one-record-at-a-time scan. -/
namespace J6R30GeneratedRootLayout
open scoped Classical
open J6Mesh J6OrientedHost J6R24LegalLayout J6R28GeneratedRootFrame
open A1R10 AOracleMachineTime AOracleMachineTimeTape
set_option maxHeartbeats 10400000
set_option maxRecDepth 1700

inductive OldFlag
  | literal (acceptingBit : Bool)
  | equal
  | free

def flagAt {d : ℕ} (g : Gate d) (i : Fin d) : OldFlag :=
  match g with
  | .clause s => .literal (s i)
  | .equal=>.equal
  | .free=>.free

structure SignedHalfPort (r c d : ℕ) where
  row : Word r
  column : Word c
  leg : Word d
  side : Bool
  flag : OldFlag

structure LiteralCodec {V : Type*} {m n : ℕ} (T : Plant V m n) (r c d : ℕ) where
  rowCode : V→Word r
  distinctRows : Function.Injective rowCode
  columnFit : n≤2^c
  portFit : ∀ v,T.degree v≤2^d

def plantHalfPort {V : Type*} {m n r c d : ℕ} (T : Plant V m n)
    (C : LiteralCodec T r c d) (u : Fin m) : SignedHalfPort r c d :=
  let x := T.rowPort.symm u
  let y := T.colPort.symm u
  ⟨C.rowCode x.1,⟨encodeBits c y.1.val,encodeBits_length _ _⟩,
    ⟨encodeBits d x.2.val,encodeBits_length _ _⟩,y.2,flagAt (T.old x.1) x.2⟩

structure LiteralPortFile {V : Type*} {m n : ℕ} (T : Plant V m n) (r c d : ℕ) where
  codec : LiteralCodec T r c d
  raw : List (SignedHalfPort r c d)
  exactFile : raw=List.ofFn (plantHalfPort T codec)

theorem LiteralPortFile.rows {V : Type*} {m n r c d : ℕ} {T : Plant V m n}
    (S : LiteralPortFile T r c d) : S.raw.length=m := by
  rw [S.exactFile,List.length_ofFn]

def seekRecord {D : Type*} (addr : List Bool) : List D→Meter (Option D)
  | []=>⟨none,4⟩
  | x::xs=>
    let s := borrowCore true addr
    if s.result.2 then ⟨some x,s.steps+2*addr.length+8⟩
    else
      let old := seekRecord s.result.1 xs
      ⟨old.result,s.steps+old.steps+2*addr.length+8⟩

theorem seek_record_exact {D : Type*} (addr : List Bool) (rows : List D) :
    (seekRecord addr rows).result=rows[bitsValue addr]? ∧
    (seekRecord addr rows).steps≤4+rows.length*(10*addr.length+8) := by
  induction rows generalizing addr with
  | nil => simp [seekRecord]
  | cons x xs ih =>
    let z := borrowCore true addr
    have W := borrow_exact true addr
    by_cases zero : z.result.2=true
    · have h : bitsValue addr=0 := (borrow_zero addr).mp zero
      simp only [seekRecord,show (borrowCore true addr).result.2=true from zero,if_true,h,
        List.getElem?_cons_zero,W.2.2,List.length_cons,Nat.succ_mul]
      exact ⟨True.intro,by omega⟩
    · have nz : z.result.2=false := by cases e : z.result.2 <;> simp_all
      have vs := borrow_decreases addr nz
      obtain ⟨e,p⟩ := ih z.result.1
      simp only [show z.result.1.length=addr.length from W.1] at p
      change (if z.result.2 then (⟨some x,z.steps+2*addr.length+8⟩ : Meter (Option D)) else
        ⟨(seekRecord z.result.1 xs).result,z.steps+(seekRecord z.result.1 xs).steps+2*addr.length+8⟩).result
        =(x::xs)[bitsValue addr]? ∧ _ 
      have N : z.steps=8*addr.length := W.2.2
      have K : (seekRecord addr (x::xs)).steps =
          z.steps+(seekRecord z.result.1 xs).steps+2*addr.length+8 := by simp [seekRecord,nz,z]
      rw [if_neg zero,K,N]
      constructor
      · rw [←vs,List.getElem?_cons_succ]
        exact e
      · change 8*addr.length+(seekRecord z.result.1 xs).steps+2*addr.length+8≤
          4+(xs.length+1)*(10*addr.length+8)
        rw [Nat.add_mul,Nat.one_mul]
        omega

def copyPortWord {d : ℕ} (w : Word d) : Meter (Word d) :=
  let x := appendBits w.val []
  ⟨⟨x.result,by
    change (appendBits w.val []).result.length=d
    rw [append_bits_exact]
    simpa only [List.append_nil] using w.property⟩,x.steps⟩

theorem port_word_copy {d : ℕ} (w : Word d) : copyPortWord w=⟨w,2+4*d⟩ := by
  have x : (copyPortWord w).result=w := Subtype.ext (by simp [copyPortWord,append_bits_exact])
  have n : (copyPortWord w).steps=2+4*d := by simp [copyPortWord,append_bits_exact,w.property]
  cases H : copyPortWord w with
  | mk v q =>
    simp only [H] at x n
    rw [x,n]

def copySeed {r c d : ℕ} (v : SignedHalfPort r c d) : Meter (SignedHalfPort r c d) :=
  let x := copyPortWord v.row
  let y := copyPortWord v.column
  let z := copyPortWord v.leg
  ⟨⟨x.result,y.result,z.result,v.side,v.flag⟩,x.steps+y.steps+z.steps+8⟩

def seedFee (r c d : ℕ) := 14+4*(r+c+d)

theorem seed_copy_exact {r c d : ℕ} (v : SignedHalfPort r c d) :
    copySeed v=⟨v,seedFee r c d⟩ := by
  cases v
  simp only [copySeed,port_word_copy,seedFee]
  congr 1
  omega

structure MountedPort (r c d : ℕ) where
  base : RootPortBase
  literal : Option (SignedHalfPort r c d)

def mountSource {r c d : ℕ} (xs : List (SignedHalfPort r c d))
    (p : RootPortBase) : Meter (MountedPort r c d) :=
  match p.origin with
  | .padding _ _ _=>⟨⟨p,none⟩,6⟩
  | .literal id _=>
    let row := seekRecord id xs
    match row.result with
    | none=>⟨⟨p,none⟩,row.steps+8⟩
    | some hit=>
      let cp := copySeed hit
      ⟨⟨p,some cp.result⟩,row.steps+cp.steps+8⟩

def mountStride (m r c d : ℕ) := 12+m*(10*RootKey m+8)+seedFee r c d

noncomputable def trueMounted {V : Type*} {m n r c d : ℕ} {T : Plant V m n}
    (P : LiteralPortFile T r c d) (e : RootWire m) : MountedPort r c d :=
  ⟨expectedBase m e,
    match e with
    | .inl (u,_)=>some (plantHalfPort T P.codec u)
    | .inr _=>none⟩

theorem mount_actual_wire {V : Type*} {m n r c d : ℕ} {T : Plant V m n}
    (P : LiteralPortFile T r c d) (e : RootWire m) :
    (mountSource P.raw (expectedBase m e)).result=trueMounted P e ∧
    (mountSource P.raw (expectedBase m e)).steps≤mountStride m r c d := by
  rcases e with (⟨u,j⟩|⟨p,side⟩)
  · let key := encodeBits (RootKey m) u.val
    let Z := seekRecord key P.raw
    have Zspec := seek_record_exact key P.raw
    have kval : bitsValue key=u.val :=
      encodeBits_exact _ _ (u.isLt.trans (root_count_high_fit m))
    have hit : Z.result=some (plantHalfPort T P.codec u) := by
      have h : Z.result=P.raw[bitsValue key]? := Zspec.1
      rw [h,kval,P.exactFile,List.getElem?_ofFn]
      simp [u.isLt]
    have reg : Z.steps≤4+m*(10*RootKey m+8) := by
      simpa only [Z,key,P.rows,encodeBits_length] using (seek_record_exact key P.raw).2
    change (match Z.result with
      | none => (⟨⟨expectedBase m (.inl (u,j)),none⟩,Z.steps+8⟩ : Meter (MountedPort r c d))
      | some hit=>⟨⟨expectedBase m (.inl (u,j)),some (copySeed hit).result⟩,Z.steps+(copySeed hit).steps+8⟩).result
        =trueMounted P (.inl (u,j)) ∧ _
    have exactFee : (mountSource P.raw (expectedBase m (.inl (u,j)))).steps=
        Z.steps+seedFee r c d+8 := by
      change (match Z.result with
        | none => (⟨⟨expectedBase m (.inl (u,j)),none⟩,Z.steps+8⟩ : Meter (MountedPort r c d))
        | some hit=>⟨⟨expectedBase m (.inl (u,j)),some (copySeed hit).result⟩,Z.steps+(copySeed hit).steps+8⟩).steps=_
      simp only [hit,seed_copy_exact]
    rw [exactFee]
    constructor
    · simp only [hit,seed_copy_exact]
      rfl
    · unfold mountStride
      omega
  · change (⟨expectedBase m (.inr (p,side)),none⟩ : MountedPort r c d)=_ ∧ 6≤_
    exact ⟨rfl,by unfold mountStride; omega⟩

def mountAll {r c d : ℕ} (xs : List (SignedHalfPort r c d)) :
    List RootPortBase→Meter (List (MountedPort r c d))
  | []=>⟨[],4⟩
  | a::as=>
    let b := mountSource xs a
    let t := mountAll xs as
    ⟨b.result::t.result,b.steps+t.steps+4⟩

theorem mount_all_exact {V : Type*} {m n r c d : ℕ} {T : Plant V m n}
    (P : LiteralPortFile T r c d) (xs : List (RootWire m)) :
    (mountAll P.raw (xs.map (expectedBase m))).result=xs.map (trueMounted P) ∧
    (mountAll P.raw (xs.map (expectedBase m))).steps≤4+xs.length*(mountStride m r c d+4) := by
  induction xs with
  | nil=>simp [mountAll]
  | cons e es ih=>
    obtain ⟨hit,bill⟩ := mount_actual_wire P e
    obtain ⟨endOK,endFee⟩ := ih
    simp only [mountAll,List.map_cons,List.length_cons,hit,endOK,Nat.succ_mul,true_and]
    omega

def generatedPaddedPorts (m : ℕ) {r c d : ℕ} (xs : List (SignedHalfPort r c d)) :
    Meter (List (MountedPort r c d)) :=
  let A := generatedBases m xs
  let B := mountAll xs A.result
  ⟨B.result,A.steps+B.steps+5⟩

def paddedPortsFee (m r c d : ℕ) := basesFee m+4+M m*(mountStride m r c d+4)+5

theorem generated_padded_ports_exact {V : Type*} {m n r c d : ℕ} {T : Plant V m n}
    (P : LiteralPortFile T r c d) :
    let S := generatedPaddedPorts m P.raw
    S.result=(actualWires m).map (trueMounted P) ∧
    S.result.length=M m ∧
    (S.result.map (fun row=>row.base.key)).Nodup ∧
    S.steps≤paddedPortsFee m r c d := by
  obtain ⟨b,l,unique,fee⟩ := generated_bases_exact m P.raw P.rows
  have H := mount_all_exact P (actualWires m)
  have C := ordered_wires_exact (constantRootWord m) (printed_room m) (printed_half_correct m)
  have N : (((actualWires m).map (trueMounted P)).map fun row=>row.base.key).Nodup := by
    rw [List.map_map]
    exact C.1.map (base_key_injective m)
  have hResult : (generatedPaddedPorts m P.raw).result=(actualWires m).map (trueMounted P) := by
    change (mountAll P.raw (generatedBases m P.raw).result).result=_
    rw [b,H.1]
  refine ⟨hResult,by rw [hResult,List.length_map,actual_wires_count],by rwa [hResult],?_⟩
  change (generatedBases m P.raw).steps+(mountAll P.raw (generatedBases m P.raw).result).steps+5≤_
  rw [b]
  have bill := H.2
  rw [actual_wires_count] at bill
  unfold paddedPortsFee
  omega

#print axioms LiteralPortFile.rows
#print axioms seek_record_exact
#print axioms seed_copy_exact
#print axioms mount_actual_wire
#print axioms generated_padded_ports_exact
end J6R30GeneratedRootLayout
