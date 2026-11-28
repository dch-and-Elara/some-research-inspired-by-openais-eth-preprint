
import A2R45LiteralSimulated
import A2R45LiteralFilledAlgebra
import A1R43LiteralGenericLayout
import J6R12RepackBoolean
import J6R11IntegralRetained

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 1700
set_option linter.unusedSectionVars false

/-! The binary EntryFile on the actual fully filled A2 star host.
Old rows read exactly their odd incidence ports; old columns read their
even ports. Every other port has its genuine unary dummy table. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial FixedHostAcquisition Acquisition
open A1R43Literal.General J6R10Repack J6R9Recursive J6R11Integral

noncomputable section
variable {n : ℕ} {Pad : Type}
abbrev NativeWire (n : ℕ) (Pad : Type) := SplitWire (Wire n) Pad
abbrev NativeRow (n : ℕ) (Pad : Type) := SplitRow (Wire n) (Row n) Pad
abbrev NativeCol (n : ℕ) (Pad : Type) := SplitCol (Wire n) (Column n) Pad
local notation "T" => simulated n

def nativeNetwork (n : ℕ) (Pad : Type) := splitNetwork (simulated n) Pad

local notation "N" => nativeNetwork n Pad

def rowsOdd (r : Row n) (i : ParentPorts T (.inl r)) :
    ParentPorts N (.inl (.inl r)) := by
  obtain ⟨(e|e),he⟩ := i
  · exact ⟨.inl (oddWire (Wire n) Pad e),congrArg (fun q : Row n=>Sum.inl (Sum.inl q)) (Sum.inl.inj he)⟩
  · cases he

def colsEven (c : Column n) (i : ParentPorts T (.inr c)) :
    ParentPorts N (.inr (.inl c)) := by
  obtain ⟨(e|e),he⟩ := i
  · cases he
  · exact ⟨.inr (evenWire (Wire n) Pad e),congrArg (fun q : Column n=>Sum.inr (Sum.inl q)) (Sum.inr.inj he)⟩

def dummyColIndex : Wire n⊕Pad → NativeWire n Pad
  | .inl e=>oddWire (Wire n) Pad e
  | .inr p=>.inr p

def zeroPin (z : Wire n⊕Pad) : ParentPorts N (.inr (.inr z)) := by
  refine ⟨.inr (dummyColIndex z),?_⟩
  cases z <;> rfl

def tableFlag (w : Input n) :
    ∀ v : NativeRow n Pad⊕NativeCol n Pad, (ParentPorts N v→Bool) → Bool
  | .inl (.inl r),x => simRowFlag w r (x ∘ rowsOdd r)
  | .inl (.inr _),_ => true
  | .inr (.inl c),x => simColFlag c (x ∘ colsEven c)
  | .inr (.inr z),x => !(x (zeroPin z))

def file (w : Input n) (f : ℤ[X]) (base : ℕ) : EntryFile f 1 N :=
  fun v=>⟨base,fun x=>if tableFlag w v x then 1 else 0⟩

theorem file_creation (w : Input n) (f : ℤ[X]) (base : ℕ)
    (v : NativeRow n Pad⊕NativeCol n Pad) :
    ((file (Pad:=Pad) w f base) v).created=base := rfl

theorem file_frozen (w : Input n) (f : ℤ[X]) (base : ℕ) (hb : 0<base)
    (hf : f.Monic) (hd : 0<f.natDegree) (v : NativeRow n Pad⊕NativeCol n Pad)
    (x : ParentPorts N v→Bool) :
    ((file (Pad:=Pad) w f base) v).frozen hf x =
      bit (tableFlag w v x) := by
  unfold file CreatedEntry.frozen bit
  exact J6R12Repack.canonical_lift_bool base hb f hf hd 1 (by decide) _

def rowFlag (w : Input n) (x : NativeWire n Pad→Bool) (r : NativeRow n Pad) : Bool :=
  tableFlag w (.inl r) (assignment N x (.inl r))

def colFlag (w : Input n) (x : NativeWire n Pad→Bool) (c : NativeCol n Pad) : Bool :=
  tableFlag w (.inr c) (assignment N x (.inr c))

theorem rowFlag_real (w : Input n) (x : NativeWire n Pad→Bool) (r : Row n) :
      rowFlag w x (.inl r)=simRowFlag w r (assignment T (oddBits x) (.inl r)) := rfl

theorem colFlag_real (w : Input n) (x : NativeWire n Pad→Bool) (c : Column n) :
      colFlag w x (.inl c)=simColFlag c (assignment T (evenBits x) (.inr c)) := by
  change simColFlag c (assignment N x (.inr (.inl c)) ∘ colsEven c) =
    simColFlag c (assignment T (evenBits x) (.inr c))
  have harg : assignment N x (.inr (.inl c)) ∘ colsEven c =
      assignment T (evenBits x) (.inr c) := by
    funext i
    obtain ⟨(u|u),hu⟩ := i
    · cases hu
    · rfl
  rw [harg]

theorem colFlag_pin (w : Input n) (x : NativeWire n Pad→Bool) (z : Wire n⊕Pad) :
      colFlag w x (.inr z)= !(x (dummyColIndex z)) := by
  cases z <;> rfl

private theorem bit_not {K : Type*} [CommRing K] (b : Bool) :
    bit (K:=K) (!b)=(if b=false then 1 else 0) := by cases b <;> rfl

variable [Fintype Pad]
theorem rowFlags_identify {K : Type*} [CommRing K] (w : Input n) (y : NativeWire n Pad→Bool) :
    (∏ r : NativeRow n Pad,bit (K:=K) (rowFlag w y r)) =
      ((Acquisition.rowProduct (rowTable w.enabled)) ∘ oddBits) y := by
  rw [Fintype.prod_sum_type]
  change (∏ r : Row n,bit (rowFlag w y (.inl r))) * (∏ _ : Wire n⊕Pad,(1:K))=_
  simp only [Finset.prod_const_one,mul_one,Function.comp_apply,Acquisition.rowProduct,
    rowFlag_real,actual_sim_row_table]

theorem colFlags_identify {K : Type*} [CommRing K] (w : Input n) (x : NativeWire n Pad→Bool) :
    (∏ c : NativeCol n Pad,bit (K:=K) (colFlag w x c)) =
      sourceColumns FixedHostAcquisition.columnTable x := by
  rw [Fintype.prod_sum_type]
  simp only [colFlag_real,actual_sim_column_table,colFlag_pin,bit_not]
  rw [Fintype.prod_sum_type,←mul_assoc]
  rfl

theorem rowProduct_receives (w : Input n) (f : ℤ[X]) (base p : ℕ) (hb : 0<base)
    (hf : f.Monic) (hd : 0<f.natDegree) (y : NativeWire n Pad→Bool) :
    reduce p f 1 (J6R11Integral.rowProduct N (file w f base) hf y) =
      ((Acquisition.rowProduct (rowTable w.enabled)) ∘ oddBits) y := by
  rw [J6R11Integral.rowProduct,map_prod,←rowFlags_identify (K:=Box f 1 p)]
  apply Finset.prod_congr rfl
  intro r _
  rw [file_frozen w f base hb hf hd]
  change reduce p f 1 (bit (rowFlag w y r))=bit (rowFlag w y r)
  cases rowFlag w y r
  · exact map_zero _
  · exact map_one _

theorem colProduct_receives (w : Input n) (f : ℤ[X]) (base p : ℕ) (hb : 0<base)
    (hf : f.Monic) (hd : 0<f.natDegree) (x : NativeWire n Pad→Bool) :
    reduce p f 1 (J6R11Integral.colProduct N (file w f base) hf x) =
      sourceColumns FixedHostAcquisition.columnTable x := by
  rw [J6R11Integral.colProduct,map_prod,←colFlags_identify (K:=Box f 1 p) w]
  apply Finset.prod_congr rfl
  intro c _
  rw [file_frozen w f base hb hf hd]
  change reduce p f 1 (bit (colFlag w x c))=bit (colFlag w x c)
  cases colFlag w x c
  · exact map_zero _
  · exact map_one _

#print axioms file_creation
#print axioms file_frozen
#print axioms rowFlag_real
#print axioms colFlag_real
#print axioms colFlag_pin
#print axioms rowFlags_identify
#print axioms colFlags_identify
#print axioms rowProduct_receives
#print axioms colProduct_receives
end
end A2R45Literal
