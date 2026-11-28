
import J6R27OriginalGateModeFlags
import J6R27OriginalGateModeNumbers
import J6R18ChildWriteMeaning

/-! Source-to-typed mode compilation for one record. The output is
the actual ModeInput consumed by the R18/R21 retained-entry evaluator.
Order is obtained from the raw arithmetic weight; shape is checked.
The ordinal code, exponent, and physical mask bit are resident inputs. -/
namespace J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R17ModeTape
open J6R18ChildWrite P11FullPacking J6R9PacketScopes

/-- Binary-to-ordinal conversion. Charge a fixed q-bit shift-and-add
at each tape cell. All intermediates fit when the input has q bits. -/
def readNatWord (q : ℕ) : List Bool→Meter ℕ
  | [] => ⟨0,1⟩
  | bit::xs =>
    let rest := readNatWord q xs
    ⟨bit.toNat+2*rest.result,rest.steps+8*q+10⟩

theorem nat_word_exact (q : ℕ) (xs : List Bool) :
    readNatWord q xs=⟨bitsValue xs,1+xs.length*(8*q+10)⟩ := by
  induction xs with
  | nil => simp [readNatWord,bitsValue]
  | cons h t ih =>
    rw [readNatWord,ih]
    simp only [bitsValue,List.length_cons,Nat.add_mul,Nat.one_mul]
    congr 1
    omega

theorem ordinal_word_fits {q : ℕ} (w : Word q) :
    (readNatWord q w.bits).result<2^q ∧
      (readNatWord q w.bits).result=w.val ∧
      (readNatWord q w.bits).steps=1+q*(8*q+10) := by
  rw [nat_word_exact,w.size]
  exact ⟨val_lt w,rfl,rfl⟩

def buildModeInput {a q b : ℕ} (i : Fin a) (p : ℕ) (fit : i.val+1≤q)
    (axis : List Bool) (origin : RawMode q) (owner : PageRef q) (group : Word 6)
    (maskBit : Bool) (code : Word b) (multiplicity : Word q) :
    Meter (Option (ModeInput a p i q)) :=
  let n := readModeNumbers fit origin
  match n.result with
  | none => ⟨none,n.steps+4⟩
  | some decoded =>
    let w := readNatWord q decoded.order.bits
    if ok : w.result<p-1 then
      let lbl := modeFlags axis origin owner group maskBit
      let c := copyFixed code
      let β := copyFixed multiplicity
      ⟨some ⟨c.result.bits,decoded.tile,⟨w.result,ok⟩,lbl.result.1,lbl.result.2,β.result⟩,
        n.steps+w.steps+lbl.steps+c.steps+β.steps+8*q+22⟩
    else ⟨none,n.steps+w.steps+8*q+12⟩

def buildModeInputCap (a i q b : ℕ) : ℕ :=
  (5*(i+1)+17*q+19)+(1+q*(8*q+10))+(36*i+60*a+10*q+326)+
    (3*b+1)+(3*q+1)+8*q+22

set_option maxHeartbeats 4200000 in
theorem actual_mode_input {a pages p q b : ℕ} (i : Fin a) (fit : i.val+1≤q)
    (hPage : pages≤2^q) (hp : p<2^q)
    (axis : List Bool) (clock : axis.length=i.val)
    (mask : MaskFamily a pages (Fin 64)) (x : PacketMode i pages (2^(i.val+1)) p)
    (page : Page a pages (Fin 64)) (g : Fin 64) (code : Word b) (mult : Word q) :
    let orig := x.1.val
    let tile := tileIndex i x.2.1
    let out := buildModeInput i p fit axis (encodeMode (q:=q) i x) (pageRef q page)
      (word g.val) (selectedMaskBit mask orig i) code mult
    ∃ M : ModeInput a p i q, out.result=some M ∧ M.code=code.bits ∧
      M.tile.val=x.2.1.val ∧ M.order=x.2.2 ∧ M.beta=mult ∧
      (M.targeted=true ↔ orig=page ∧ rowGroup mask i (orig,tile)=g) ∧
      (M.sourced=true ↔ orig=page ∧ colGroup mask i (orig,tile)=g) ∧
      out.steps≤buildModeInputCap a i.val q b := by
  let raw := encodeMode (q:=q) i x
  let n := readModeNumbers fit raw
  let lbl := modeFlags axis raw (pageRef q page) (word g.val) (selectedMaskBit mask x.1.val i)
  let od : Word q := word x.2.2.val
  let d := readNatWord q od.bits
  have nE : n.result=some ⟨word x.2.1.val,od⟩ ∧ n.steps=5*(i.val+1)+17*q+19 :=
    actual_mode_numbers i fit hp x
  have rO : od.val=x.2.2.val :=
    word_val ((x.2.2.isLt.trans_le (Nat.sub_le p 1)).trans hp)
  obtain ⟨_,dE,dC⟩ := ordinal_word_fits od
  change d.result=od.val at dE
  change d.steps=_ at dC
  have order : d.result=x.2.2.val := dE.trans rO
  have range : d.result<p-1 := order.symm ▸ x.2.2.isLt
  have W := actual_mode_flags i (by omega : i.val<q) axis clock hPage mask x page g
  let M : ModeInput a p i q := ⟨code.bits,word x.2.1.val,⟨d.result,range⟩,lbl.result.1,lbl.result.2,mult⟩
  refine ⟨M,?_,rfl,word_val x.2.1.isLt,Fin.ext order,rfl,W.1,W.2.1,?_⟩
  · unfold buildModeInput
    dsimp only
    rw [nE.1]
    dsimp only
    rw [dif_pos range,copy_fixed_exact,copy_fixed_exact]
  · unfold buildModeInput
    dsimp only
    rw [nE.1]
    dsimp only
    rw [dif_pos range,copy_fixed_exact,copy_fixed_exact]
    change n.steps+d.steps+lbl.steps+(3*b+1)+(3*q+1)+8*q+22≤_
    rw [nE.2,dC]
    have F : lbl.steps≤36*i.val+60*a+10*q+326 := W.2.2
    unfold buildModeInputCap
    omega

#print axioms nat_word_exact
#print axioms ordinal_word_fits
#print axioms actual_mode_input
end J6R27OriginalGate



