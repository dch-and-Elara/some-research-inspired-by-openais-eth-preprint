
import J6R25PreparedSupplyProducer
import J6R21AncestorDirectory

/-! Equality of fully serialized mode keys. The two orientations of an
unordered packet type are not merged; both ordered cell words, the
copy, the tile and the positive weight are compared. -/
namespace J6R27OriginalGate
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R21Ancestor

def eqRawBits : List Bool→List Bool→Meter Bool
  | [],[] => ⟨true,2⟩
  | [],_::_ => ⟨false,2⟩
  | _::_,[] => ⟨false,2⟩
  | a::as,b::bs =>
    let z := eqRawBits as bs
    ⟨(a == b) && z.result,z.steps+5⟩

theorem eq_raw_bits_exact (as bs : List Bool) :
    ((eqRawBits as bs).result=true↔as=bs) ∧
    (eqRawBits as bs).steps≤5*as.length+2 := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [eqRawBits]
  | cons a as ih =>
    cases bs with
    | nil => simp [eqRawBits]
    | cons b bs =>
      have h := ih bs
      constructor
      · simp only [eqRawBits,Bool.and_eq_true,beq_iff_eq,h.1,List.cons.injEq]
      · change (eqRawBits as bs).steps+5≤5*(as.length+1)+2
        omega

def cmpMode {q : ℕ} (a b : RawMode q) : Meter Bool :=
  let l := eqRawBits a.key.1 b.key.1
  let r := eqRawBits a.key.2 b.key.2
  let p := cmpAddr a.page b.page
  let t := cmpAddr a.tile b.tile
  let w := cmpAddr a.weight b.weight
  ⟨l.result && r.result && p.result && t.result && w.result,
    l.steps+r.steps+p.steps+t.steps+w.steps+12⟩

theorem cmp_mode_exact {q : ℕ} (a b : RawMode q) :
    ((cmpMode a b).result=true↔a=b) ∧
    (cmpMode a b).steps≤5*a.key.1.length+5*a.key.2.length+30*q+31 := by
  have hL := eq_raw_bits_exact a.key.1 b.key.1
  have hR := eq_raw_bits_exact a.key.2 b.key.2
  have hP := cmpAddr_exact a.page b.page
  have hT := cmpAddr_exact a.tile b.tile
  have hW := cmpAddr_exact a.weight b.weight
  constructor
  · simp only [cmpMode,Bool.and_eq_true,hL.1,hR.1,hP.1,hT.1,hW.1]
    constructor
    · rintro ⟨⟨⟨⟨h1,h2⟩,hp⟩,ht⟩,hw⟩
      have key : a.key=b.key := Prod.ext h1 h2
      cases a
      cases b
      simp_all
    · rintro rfl
      exact ⟨⟨⟨⟨rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩
  · simp only [cmpMode,hP.2,hT.2,hW.2]
    have L := hL.2
    have R := hR.2
    omega

def copyFixed {q : ℕ} (a : Word q) : Meter (Word q) :=
  let p := copyBytes a.bits
  ⟨⟨p.result,by
    change (copyBytes a.bits).result.length=q
    rw [copyBytes_exact]
    exact a.size⟩,p.steps⟩

theorem copy_fixed_exact {q : ℕ} (a : Word q) :
    copyFixed a=⟨a,3*q+1⟩ := by
  have h := copyBytes_exact a.bits
  have e : (copyFixed a).result.bits=a.bits := by
    change (copyBytes a.bits).result=a.bits
    rw [h]
  have r : (copyFixed a).result=a := by
    cases a
    unfold copyFixed
    simp only [Word.mk.injEq]
    exact e
  have s : (copyFixed a).steps=3*q+1 := by
    change (copyBytes a.bits).steps=_
    rw [h,a.size]
  generalize en : copyFixed a=z at r s ⊢
  rcases z with ⟨res,paid⟩
  change res=a at r
  change paid=3*q+1 at s
  subst res
  subst paid
  rfl

#print axioms eq_raw_bits_exact
#print axioms cmp_mode_exact
#print axioms copy_fixed_exact
end J6R27OriginalGate


