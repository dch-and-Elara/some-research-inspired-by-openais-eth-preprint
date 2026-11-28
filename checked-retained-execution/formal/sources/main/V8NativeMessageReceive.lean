import V8NativeMessageGroups
import V8NativeMessageFixed

/-! The fixed-coordinate row message reconstructs the exact projection
of the same high-source completed addresses, with the receiver's own
signs as a separate argument. No access to foreign group flags is a
decoder parameter. -/
namespace V8NativeMessage.Five
open scoped Polynomial BigOperators Classical
open Polynomial P11FullPacking J6R10Repack J6R9Recursive DenominatorBudget J6R10Integral
open V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu V8PooledMenu.FiveCopy

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G}
  {f : ℤ[X]}

def physIndex (i : Fin (rootU V)) : Fin (rootA V) :=
  i.castLE (by unfold rootA; omega)

variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
  (i : Fin (rootU V)) (T : Finset (Fin 64))

local notation "Sites" => FixedSites hu huM (rootA V) i

theorem actual_index (t : Sites) : rootIndex hu huM t.val=physIndex i := by
  apply Fin.ext
  change (level hu huM t.val).val=i.val
  exact congrArg Fin.val t.property

abbrev RowWords :=
  {v : V // switchGroup P (physIndex i) v∈T} → Bool

abbrev ColWords :=
  {v : V // switchGroup P (physIndex i) v∉T} → Bool

def rowFill (x : RowWords P i T) (v : V) : Bool :=
  if h : switchGroup P (physIndex i) v∈T then x ⟨v,h⟩ else false

def colFill (y : ColWords P i T) (v : V) : Bool :=
  if h : switchGroup P (physIndex i) v∈T then false else y ⟨v,h⟩

def signs (x : RowWords P i T) (y : ColWords P i T) (v : V) : Bool :=
  if h : switchGroup P (physIndex i) v∈T then x ⟨v,h⟩ else y ⟨v,h⟩

def rowPoly (t : Sites) (x : RowWords P i T) : TwoLocal[X] :=
  partPoly P (rootIndex hu huM t.val) t.val.val T (flags G p (rowFill P i T x))

def colPoly (t : Sites) (y : ColWords P i T) : TwoLocal[X] :=
  partPoly P (rootIndex hu huM t.val) t.val.val Tᶜ (flags G p (colFill P i T y))

theorem signs_poly_split (t : Sites) (x : RowWords P i T) (y : ColWords P i T) :
    wholeScaled P (rootIndex hu huM t.val) t.val.val (flags G p (signs P i T x y)) =
      rowPoly P hu huM i T t x*colPoly P hu huM i T t y := by
  rw [whole_split P _ _ T]
  apply congrArg₂ (·*·)
  · apply part_switch_local
    intro v h
    rw [actual_index hu huM i t] at h
    simp only [signs,rowFill,dif_pos h]
  · apply part_switch_local
    intro v h
    rw [actual_index hu huM i t] at h
    have hh := Finset.mem_compl.mp h
    simp only [signs,colFill,dif_neg hh]

variable (L : PublicPrecision V)

abbrev RowTape := FixedTape hu huM (rootA V) L.prec i

abbrev FixedMenu (f : ℤ[X]) :=
  (t : Sites) → Address P hu huM t.val → Residue f 1 (low hu huM L t.val)

def fixedNative (probes : Probes V f) (hf : f.Monic) (s : V → Bool) :
    FixedMenu P hu huM i L f :=
  fun t adr => nativeMenu P hu huM L probes hf s t.val adr

def rowMessage (x : RowWords P i T) : RowTape hu huM i L :=
  fun t => digits (low hu huM L t.val) (rowPoly P hu huM i T t x)

/-- Both the original high address and its original high tuple are
kept unchanged. Only the scalar received from that completed slot is
projected. The receiver may freely evaluate its own input side. -/
def rowDecoder (probes : Probes V f) (msg : RowTape hu huM i L)
    (y : ColWords P i T) : FixedMenu P hu huM i L f :=
  fun t adr =>
    if adr.beta=0 then
      let n := low hu huM L t.val
      let z := readProbe f n (probes.word t.val adr.probeIdx)
      TruncatedProbeMenu.reconstruct (msg t) z *
        (colPoly P hu huM i T t y).eval₂
          (J6ZeroTransport.reduceAt n (box_two_nil n f 1)) (2*z)
    else 0

/-- N8 on the actual native receiver: every legal complete slot at the
fixed coordinate is determined by the row tape and the true column signs. -/
theorem N8_native (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree)
    (x : RowWords P i T) (y : ColWords P i T) :
    fixedNative P hu huM i L probes hf (signs P i T x y)=
      rowDecoder P hu huM i T L probes (rowMessage P hu huM i T L x) y := by
  funext t adr
  unfold fixedNative
  rw [nativeMenu_eq P hu huM L probes hf hd]
  by_cases h : adr.beta=0
  · simp only [decodeWhole,rowDecoder,if_pos h]
    change TruncatedProbeMenu.reconstruct
      (digits (low hu huM L t.val)
        (wholeScaled P (rootIndex hu huM t.val) t.val.val (flags G p (signs P i T x y)))) _ =
      TruncatedProbeMenu.reconstruct
        (digits (low hu huM L t.val) (rowPoly P hu huM i T t x)) _ * _
    let n := low hu huM L t.val
    have hnil := box_two_nil n f 1
    rw [signs_poly_split P hu huM i T t x y,
      receive_digits hnil (J6ZeroTransport.reduceAt n hnil),
      receive_digits hnil (J6ZeroTransport.reduceAt n hnil), Polynomial.eval₂_mul]
  · simp only [decodeWhole,rowDecoder,if_neg h]

theorem N8_row_alphabet : Fintype.card (RowTape hu huM i L)=
    2^fixedBits (rootA V) i (L.prec i) :=
  fixedTape_card hu huM (by unfold rootA; omega) L.prec i

#print axioms actual_index
#print axioms signs_poly_split
#print axioms rowMessage
#print axioms N8_native
#print axioms N8_row_alphabet
end
end V8NativeMessage.Five
