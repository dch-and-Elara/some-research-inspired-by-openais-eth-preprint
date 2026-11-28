import V8NativeMessageN4Local
import V8NativeMessageC3Canonical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000

/-! Actual original four-copy D1 root/slot precision and the canonical
whole-product exchange, using this slot's actual native recursive
replies and not a five-copy schedule. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open P11FullPacking Paper5.D1Literal Paper5.HybridClosure J6R12Blueprint J6ActiveRun
  J6ActiveSchedule J6R9Recursive J6R10Repack J6R10Integral J1PPrinted
open V8NativeMessage.C3.Canonical
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
  {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f}

local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => oldRowRoot F reg f (fun _=>false)

def widthU (F : Finset (W×W)) : ℕ := stepU (Nat.clog 2 (oldRowSize F)) 0

omit [DecidableEq W] in
theorem width_precisionBits :
    (S).levelBits 0=2*widthU F := by
  change stepA (Nat.clog 2 (oldRowSize F)) 0=2*widthU F
  simp [stepA,widthU]

def nodeScale (t : PublicCenter F reg f) : ℕ :=
  2^(2*widthU F)/2^padicValInt 2 t.val

theorem four_copy_precision (t : PublicCenter F reg f) :
    registerPrecision S r* t =
      (4*Fintype.card W+1) +
      8*height (24*Fintype.card W) (widthU F)*nodeScale t +
      8*(24*Fintype.card W)*(2*widthU F+1) := by
  change J9PrintedSchedule.precision (4*Fintype.card W+1)
    (height (Fintype.card (DWire F)) (widthU F))
    (2^(S).levelBits 0/2^padicValInt 2 t.val)
    (Fintype.card (DWire F)) ((S).levelBits 0)=_
  rw [d_physical_wire_count F reg,width_precisionBits]
  rfl

variable (d : LayoutReady F reg f) (hf : f.Monic) (slot : PublicSlot F reg f P d)

def receiveChild (σ : W→Bool) (g : Fin 64) : Residue f 1 (registerPrecision S r* slot.1) :=
  publicReply F reg f P d hf σ ⟨slot.1,slot.2.1,slot.2.2,g⟩

def rawWhole (σ : W→Bool) : IntRing f 1 :=
  canonicalLift (registerPrecision S r* slot.1) f hf 1
    (∏ g, receiveChild d hf slot σ g)

def rawSeparate (σ : W→Bool) : IntRing f 1 :=
  ∏ g, representative (registerPrecision S r* slot.1) f 1 (receiveChild d hf slot σ g)

theorem literal_whole_separate (q : ℕ) (b : RatRing f 1) (σ : W→Bool)
    (hb : ShiftedIntegral f 1 (registerPrecision S r* slot.1) q b) :
    ∃ e : IntRing f 1, b*(embed f 1 (rawWhole d hf slot σ)-embed f 1 (rawSeparate d hf slot σ)) =
      embed f 1 ((2:IntRing f 1)^q*e) :=
  actual_separate_transfer (registerPrecision S r* slot.1) f hf 1 q (receiveChild d hf slot σ)
    (fun g => representative _ f 1 (receiveChild d hf slot σ g))
    (fun _ => representative_spec _ f 1 _) b hb

theorem literal_whole_loss_exchange (Lm Ld : ℕ) (m w : RatRing f 1)
    (hm : HasLoss f 1 Lm m) (hw : HasLoss f 1 Ld w) (σ : W→Bool)
    (fit : Lm≤2*height (24*Fintype.card W) (widthU F)*nodeScale slot.1+
      4*(24*Fintype.card W)*(2*widthU F+1))
    (ld : Ld≤6*height (24*Fintype.card W) (widthU F)*nodeScale slot.1+
      4*(24*Fintype.card W)*(2*widthU F+1)) :
    ∃ e : IntRing f 1,
      (w*m)*(embed f 1 (rawWhole d hf slot σ)-embed f 1 (rawSeparate d hf slot σ)) =
        embed f 1 ((2:IntRing f 1)^(4*Fintype.card W+1)*e) := by
  apply literal_whole_separate d hf slot _ _ σ
  apply loss_suffices (loss_mul hw hm)
  rw [four_copy_precision]
  let h := height (24*Fintype.card W) (widthU F)
  let n := nodeScale slot.1
  let m := 24*Fintype.card W
  let q := 2*widthU F+1
  change 4*Fintype.card W+1+(Ld+Lm) ≤ 4*Fintype.card W+1+8*h*n+8*m*q
  calc
    _ ≤ 4*Fintype.card W+1+((6*h*n+4*m*q)+(2*h*n+4*m*q)) :=
      Nat.add_le_add_left (Nat.add_le_add ld fit) _
    _ = _ := by ring

#print axioms width_precisionBits
#print axioms four_copy_precision
#print axioms literal_whole_separate
#print axioms literal_whole_loss_exchange
end
end V8NativeMessage.N4
