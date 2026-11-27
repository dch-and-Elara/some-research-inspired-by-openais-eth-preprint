import BareissPaperTraceCost

namespace Paper3.BareissBit

open Reconstruction.BareissSolver Reconstruction.BareissPaper
open AffineCost.Bit (Run Signed)

def Decodes (B : ℕ) (op : ScalarOp) : Prop :=
  (scalarProgram B op).value.map (Sum.map id Signed.number) = some (scalarValue op)

def ValidTrace (B : ℕ) (ops : List ScalarOp) : Prop :=
  ∀ op ∈ ops, Decodes B op

def paidZero (B : ℕ) (a : ℤ) : Run Bool :=
  let r := scalarProgram B (.testZero a)
  ⟨(match r.value with | some (.inl b) => b | _ => false), r.steps + 2⟩

def paidInt (B : ℕ) (op : ScalarOp) : Run ℤ :=
  let r := scalarProgram B op
  match r.value with
  | some (.inr x) =>
    let out := readSigned x
    ⟨out.value, r.steps + out.steps + 2⟩
  | _ => ⟨0,r.steps + 2⟩

theorem paidZero_correct {B : ℕ} {a : ℤ} (h : Decodes B (.testZero a)) :
    (paidZero B a).value = decide (a = 0) := by
  unfold Decodes at h
  cases hv : (scalarProgram B (.testZero a)).value with
  | none => simp [hv] at h
  | some z =>
    cases z with
    | inl b =>
      have e : b = decide (a = 0) := by simpa [hv,scalarValue] using h
      simp [paidZero,hv,e]
    | inr x => simp [hv,scalarValue] at h

theorem paidInt_correct {B : ℕ} {op : ScalarOp} {z : ℤ}
    (h : Decodes B op) (hz : scalarValue op = .inr z) :
    (paidInt B op).value = z := by
  unfold Decodes at h
  cases hv : (scalarProgram B op).value with
  | none => simp [hv] at h
  | some v =>
    cases v with
    | inl b => simp [hv,hz] at h
    | inr x =>
      have e : x.number = z := by simpa [hv,hz] using h
      simp [paidInt,hv,e]

theorem scalar_output_size (B : ℕ) (op : ScalarOp) (z : Signed)
    (hz : (scalarProgram B op).value = some (.inr z)) : z.size ≤ 2*B+1 := by
  cases op with
  | testZero a => cases hz
  | mul a b =>
    change some (Sum.inr (α := Bool) (Signed.mul (writeSigned B a).value (writeSigned B b).value).value) =
      some (.inr z) at hz
    have h := (Option.some.inj hz)
    have h' := Sum.inr.inj h
    rw [← h']
    exact (Signed.mul_size _ _).trans (by
      have ha := writeSigned_size B a
      have hb := writeSigned_size B b
      omega)
  | add a b =>
    change some (Sum.inr (α := Bool) (Signed.add (writeSigned B a).value (writeSigned B b).value).value) =
      some (.inr z) at hz
    have h := (Option.some.inj hz)
    have h' := Sum.inr.inj h
    rw [← h']
    exact (Signed.add_size _ _).trans (by
      have ha := writeSigned_size B a
      have hb := writeSigned_size B b
      omega)
  | sub a b =>
    change some (Sum.inr (α := Bool) (Reconstruction.BareissArithmetic.subtract
      (writeSigned B a).value (writeSigned B b).value).value) = some (.inr z) at hz
    have h := (Option.some.inj hz)
    have h' := Sum.inr.inj h
    rw [← h']
    exact (Reconstruction.BareissArithmetic.subtract_size _ _).trans (by
      have ha := writeSigned_size B a
      have hb := writeSigned_size B b
      omega)
  | exactDiv a b =>
    let f := Reconstruction.BareissArithmetic.exactDiv (writeSigned B a).value (writeSigned B b).value
    change f.value.map (Sum.inr (α := Bool)) = some (.inr z) at hz
    have he : f.value = some z := by
      cases hf : f.value with
      | none => simp [hf] at hz
      | some x =>
        have h : x=z := by simpa [hf] using hz
        rw [h]
    have hs := (Reconstruction.BareissArithmetic.exactDiv_sound he).2.2.2
    exact hs.trans ((writeSigned_size B a).trans (by omega))

def cellPrice (B : ℕ) : ℕ := scalarBudget B + 128*(2*B+2)^2 + 2

theorem paidZero_price (B : ℕ) (a : ℤ) : (paidZero B a).steps ≤ cellPrice B := by
  simp only [paidZero,cellPrice]
  have h := scalarProgram_steps B (.testZero a)
  omega

theorem paidInt_price (B : ℕ) (op : ScalarOp) : (paidInt B op).steps ≤ cellPrice B := by
  have h := scalarProgram_steps B op
  unfold paidInt cellPrice
  dsimp only
  cases e : (scalarProgram B op).value with
  | none => simp only [Nat.add_le_add_iff_right]; omega
  | some v =>
    cases v with
    | inl b => simp only [Nat.add_le_add_iff_right]; omega
    | inr z =>
      have hz := readSigned_steps z (2*B+1) (scalar_output_size B op z e)
      change (scalarProgram B op).steps + (readSigned z).steps + 2 ≤ _
      rw [show 2*B+1+1 = 2*B+2 by omega] at hz
      omega

end Paper3.BareissBit

#print axioms Paper3.BareissBit.paidZero_correct
#print axioms Paper3.BareissBit.paidInt_correct
#print axioms Paper3.BareissBit.scalar_output_size
#print axioms Paper3.BareissBit.paidZero_price
#print axioms Paper3.BareissBit.paidInt_price

