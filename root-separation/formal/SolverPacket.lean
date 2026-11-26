import SolverRecursion
import S11NativeModes
import S11NativeWindow
import S11TupleCodec

noncomputable section
namespace RootSeparation.Solver

open S11 Polynomial
open scoped BigOperators

section ActualPacket

variable {f : ℤ[X]} {s : ℕ} {c : Call f}
variable (G : CallLayout s c) (t : callCenters s c)

abbrev ActualMode := Mode (G.packing.mixedAt t.val) (level t.val) (callPrecision s c t.val)

/-- Fixed orientation convention from the chosen packing. -/
def tileSource (z : ActualMode G t) : Fin 64 :=
  let pair := G.packing.pair z.1.val (G.coord t)
  if z.2.1.val.testBit (level t.val) then pair.1 else pair.2

def tileTarget (z : ActualMode G t) : Fin 64 :=
  let pair := G.packing.pair z.1.val (G.coord t)
  if z.2.1.val.testBit (level t.val) then pair.2 else pair.1

theorem tile_crossing_bit (x y : c.network.Wire)
    (h : (G.packing.position x).1 = (G.packing.position y).1)
    (cross : (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t)) :
    (G.packing.position x).2.val.testBit (level t.val) =
      (G.packing.position y).2.val.testBit (level t.val) := by
  have hx := G.packing.orientation x (G.coord t)
  have hy := G.packing.orientation y (G.coord t)
  change _ = (if (G.packing.position x).2.val.testBit (level t.val) then
      (G.packing.pair (G.packing.position x).1 (G.coord t)).swap else _) at hx
  change _ = (if (G.packing.position y).2.val.testBit (level t.val) then
      (G.packing.pair (G.packing.position y).1 (G.coord t)).swap else _) at hy
  rw [h] at hx
  cases bx : (G.packing.position x).2.val.testBit (level t.val) <;>
    cases by' : (G.packing.position y).2.val.testBit (level t.val) <;>
    rw [bx] at hx <;> rw [by'] at hy <;> dsimp at hx hy
  all_goals exact (cross ((congrArg Prod.fst hx).trans (congrArg Prod.snd hy).symm)).elim

open Classical in
/-- Every exponent is read in the same order as the streaming iterator.
    Choices of ordering among equal weights follow S11.modes. -/
def actualExponent (β : List ℕ) : ActualMode G t → ℕ :=
  readExponent (modes (G.packing.mixedAt t.val) (level t.val) (callPrecision s c t.val)) β

variable {K : Type*} [Field K] [CharZero K]

def nodeProbe (ζ : K) : K := (t.val:K) + shiftScale K (callA s c) * ζ

abbrev PacketPort (g : Fin 64) (k : G.Packet) :=
  {w // packetEndpoint c.network G.left G.right (G.coord t) g G.packing.position w = k}

def isColumn {g : Fin 64} {k : G.Packet} (w : PacketPort G t g k) := w.val.val.2

def wireOf {g : Fin 64} {k : G.Packet} (w : PacketPort G t g k) := w.val.val.1

def slotOf {g : Fin 64} {k : G.Packet} (w : PacketPort G t g k) : Fin (callL s c) :=
  (G.packing.position (wireOf G t w)).2

def localForm (ζ : K) {g : Fin 64} {k : G.Packet}
    (bits : PacketPort G t g k → Bool) (x : {w : PacketPort G t g k // isColumn G t w = false}) : K := by
  classical
  exact ∑ y : {w : PacketPort G t g k // isColumn G t w = true},
    (packetKernel K (callL s c) (slotOf G t x.val) (slotOf G t y.val)).eval (nodeProbe t ζ) *
      (bits y.val).toNat

def crossingCoeff (ζ : K) {g : Fin 64} {k : G.Packet}
    (x : {w : PacketPort G t g k // isColumn G t w = false}) (z : ActualMode G t) : K :=
  let δ := nodeProbe t ζ - (z.2.1.val:K) + (slotOf G t x.val).val
  ((shiftedNumerator K (callA s c) t.val).eval ζ / δ) *
    ((2:K)^(level t.val+1) / δ)^z.2.2.val

def sourceTile {g : Fin 64} {k : G.Packet} (bits : PacketPort G t g k → Bool)
    (z : ActualMode G t) : K := by
  classical
  exact ∑ y : {w : PacketPort G t g k // isColumn G t w = true},
    if (slotOf G t y.val).val % 2^(level t.val+1) = z.2.1.val then
      (((slotOf G t y.val).val / 2^(level t.val+1) : ℕ):K)^z.2.2.val * (bits y.val).toNat
    else 0

/-- Frozen packet entry formula on actual retained ports.
    The coefficient is formed from signed affine literals; tile powers
    use only columns in the same packet/group. -/
def nativePacket (ζ : K) (β : List ℕ) (g : Fin 64) (k : G.Packet)
    (bits : PacketPort G t g k → Bool) : K := by
  classical
  let row (x : {w : PacketPort G t g k // isColumn G t w = false})
      (z : Option {z : ActualMode G t // z.1.val = k ∧ tileTarget G t z = g}) : K :=
    match z with
    | none =>
      if bits x.val then localForm G t ζ bits x else 1 - localForm G t ζ bits x
    | some z =>
      if bits x.val then crossingCoeff G t ζ x z.val else -crossingCoeff G t ζ x z.val
  exact packetValue row (fun z => actualExponent G t β z.val)
    (fun z : {z : ActualMode G t // z.1.val = k ∧ tileSource G t z = g} =>
      sourceTile G t bits z.val) (fun z => actualExponent G t β z.val)

theorem crossing_kernel_integral (v : AddValuation K (WithTop ℤ)) (h₂ : v (2:K) = 1)
    (ζ : K) (hζ : 0 ≤ v ζ) (x y : c.network.Wire)
    (h : (G.packing.position x).1 = (G.packing.position y).1)
    (cross : (G.packing.cell x).1 (G.coord t) ≠ (G.packing.cell y).2 (G.coord t)) :
    let i := level t.val
    let posx := (G.packing.position x).2
    let posy := (G.packing.position y).2
    let d := (((t.val-(posy.val % 2^(i+1):ℕ)+posx.val:ℤ):K)
      + shiftScale K (callA s c) * ζ)
    let base := (shiftedNumerator K (callA s c) t.val).eval ζ / d
    let ratio := (2:K)^(i+1) / d
    (∀ b : ℕ, ∃ q : K, 0 ≤ v q ∧ base * ratio^b = 2^(b+1) * q) ∧
      ∃ err : K, 0 ≤ v err ∧
        (packetKernel K (callL s c) posx posy).eval (nodeProbe t ζ) -
        ∑ b ∈ Finset.range (callPrecision s c t.val-1),
          base * ratio^b * ((posy.val / 2^(i+1) : ℕ):K)^b =
        2^(callPrecision s c t.val) * err := by
  exact crossing_modes_native v h₂ (Nat.le_of_lt (G.coord t).isLt)
    (active_mem_grid t) (active_ne_zero t) rfl _ _ (tile_crossing_bit G t x y h cross)
    ζ hζ _ (callPrecision_pos s c t.val)

end ActualPacket

#print axioms tile_crossing_bit
#print axioms nativePacket
#print axioms crossing_kernel_integral

end RootSeparation.Solver
