import P5MainIteratorScheduledUpper

/-! Lift the numerical upper bound back to the literal native full box.
The actual row count includes all copied exceptional rows and all r groups. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real

variable {E V F Copy I B : Type*} [Fintype E] [Fintype V]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def literalBoxSlots (keep : ℕ→Prop) (Lyt : SourceLayout E V F Copy I B)
    (q : ℕ) : ℕ :=
  ∑ t : I, ((TaylorList V q).card *
    (2*Fintype.card (WordCell I B)+1)^(Fintype.card B *
      Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep)) *
    ∑ g : B,2^Fintype.card {v : V // Lyt.a v t=g})

theorem literal_box_slots_count (keep : ℕ→Prop) (Lyt : SourceLayout E V F Copy I B)
    (q b : ℕ)
    (hcell : Fintype.card (WordCell I B)≤Fintype.card E)
    (hbalanced : ∀ t g,Fintype.card {v : V // Lyt.a v t=g}≤b) :
    literalBoxSlots keep Lyt q ≤
      Fintype.card I*(TaylorList V q).card*
      (2*Fintype.card E+1)^(Fintype.card B *
        Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep)) *
      Fintype.card B*2^b := by
  let w := Fintype.card B*Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep)
  let Y := (2*Fintype.card E+1)^w
  have hy : (2*Fintype.card (WordCell I B)+1)^w≤Y := Nat.pow_le_pow_left (by omega) w
  unfold literalBoxSlots
  calc
    _ ≤ ∑ _t : I,((TaylorList V q).card*Y*(Fintype.card B*2^b)) := by
      apply Finset.sum_le_sum
      intro t _
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ hy)
      calc
        _ ≤ ∑ _g : B,2^b := Finset.sum_le_sum (fun g _ =>
          Nat.pow_le_pow_right (by decide) (hbalanced t g))
        _ = _ := by simp
    _ = _ := by simp [Nat.mul_assoc,Y,w]

set_option maxHeartbeats 5600000 in
theorem scheduled_native_full_scan (keep : ℕ→Prop) (Lyt : SourceLayout E V F Copy I B)
    (q b : ℕ) (L l Cq Cd Cm Cg : ℝ)
    (hcell : Fintype.card (WordCell I B)≤Fintype.card E)
    (hbalanced : ∀ t g,Fintype.card {v : V // Lyt.a v t=g}≤b)
    (hQ : 0<Fintype.card I) (hr : 0<Fintype.card B) (hL : 0<L) (hl : 1≤l) (heq : l=log L)
    (hρ : l/sqrt L≤1)
    (hqC : 0≤Cq) (hCd : 0≤Cd) (hCm : 0≤Cm)
    (hq : (q:ℝ)≤Cq*(Fintype.card V:ℝ)*(l/sqrt L))
    (hLbudget : L≤(Fintype.card V:ℝ)*(l^2/sqrt L))
    (hQlog : log (Fintype.card I:ℝ)≤L) (hrlog : log (Fintype.card B:ℝ)≤L)
    (hR : (1:ℝ)/(Fintype.card B:ℝ)≤Cg*(l^2/sqrt L))
    (hb : (b:ℝ)≤2*(Fintype.card V:ℝ)/(Fintype.card B:ℝ))
    (hcoord : (Fintype.card B:ℝ)*
      (Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep):ℝ)≤
      Cd*((Fintype.card V:ℝ)/((Fintype.card B:ℝ)*L)))
    (hm : log (2*(Fintype.card E:ℝ)+1)≤Cm*L) :
    (literalBoxSlots keep Lyt q:ℝ) ≤
      exp ((4+Cq/2+(Cd*Cm+2*log 2)*Cg)*(Fintype.card V:ℝ)*(l^2/sqrt L)) := by
  have hh := scheduled_full_box_upper (V:=V) q (Fintype.card I) (Fintype.card B) b
    (Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep)) (Fintype.card E)
    L l Cq Cd Cm Cg hQ hr hL hl heq hρ hqC hCd hCm hq hLbudget hQlog hrlog hR hb hcoord hm
  have hNat := literal_box_slots_count keep Lyt q b hcell hbalanced
  have hReal : (literalBoxSlots keep Lyt q:ℝ) ≤
      ((Fintype.card I*(TaylorList V q).card*(2*Fintype.card E+1)^(Fintype.card B *
        Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep))*Fintype.card B*2^b:ℕ):ℝ) := by
    exact_mod_cast hNat
  exact hReal.trans hh

#print axioms literal_box_slots_count
#print axioms scheduled_native_full_scan
end P5MainIterator
