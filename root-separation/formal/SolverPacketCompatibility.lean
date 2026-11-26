import SolverIntegralArithmetic
import SolverNativeAffine

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial Classical
open scoped BigOperators

variable {e : ℕ} (F : SourcePolynomial e) {s : ℕ} {c : Call F.f}
variable (G : CallLayout s c) (cap : probeCount c.edges (callL s c) ≤ 2^e)
variable (t : callCenters s c) (j : callProbes s c)

abbrev SourceAt (g : Fin 64) (k : G.Packet) :=
  {z : ActualMode G t // z.1.val = k ∧ tileSource G t z = g}

def integralRow (g : Fin 64) (k : G.Packet) (X : GroupBits F G t g)
    (x : LocalRows F G t g k) (o : Option (TargetAt F G t g k)) : integralElements F :=
  (2 : integralElements F) ^ o.elim' 0 (fun z => z.val.2.2.val+1) *
    ⟨normalizedEntry F G cap t j X x o,normalizedEntry_integral F G cap t j X x o⟩

def integralRead (g : Fin 64) (k : G.Packet) (X : GroupBits F G t g)
    (z : SourceAt F G t g k) : integralElements F :=
  ⟨sourceTile (K := RationalCoefficients F) G t (packetBits F G t (k := k) X) z.val,
    sourceTile_integral G t (K := RationalCoefficients F) (rationalValuation F)
      (packetBits F G t (k := k) X) z.val⟩

def integralPacket (β : List ℕ) (g : Fin 64) (k : G.Packet) (X : GroupBits F G t g) :
    integralElements F :=
  packetValue (integralRow F G cap t j g k X)
    (fun z => actualExponent G t β z.val)
    (integralRead F G t g k X) (fun z => actualExponent G t β z.val)

theorem integralPacket_value (β : List ℕ) (g : Fin 64) (k : G.Packet) (X : GroupBits F G t g) :
    (integralPacket F G cap t j β g k X).val =
      nativeEntryValue F G cap t j β g k (packetBits F G t (k := k) X) := by
  change (integralElements F).subtype (integralPacket F G cap t j β g k X) = _
  rw [integralPacket,map_packetValue]
  unfold nativeEntryValue nativePacket
  congr 1
  · funext x o
    cases o with
    | none => simp [integralRow, normalizedEntry]
    | some z =>
      let K := RationalCoefficients F
      let q := crossingCoeff G t (callPoint F cap j) x z.val
      let w := z.val.2.2.val+1
      have h : (2:K)^w ≠ 0 := pow_ne_zero _ (NeZero.ne 2)
      change ((2:K)^w * (if packetBits F G t (k := k) X x.val then q / (2:K)^w else -(q / (2:K)^w))) =
        (if packetBits F G t (k := k) X x.val then q else -q)
      by_cases hb : packetBits F G t (k := k) X x.val = true
      · rw [if_pos hb,if_pos hb,mul_div_cancel₀ _ h]
      · rw [if_neg hb,if_neg hb,mul_neg,mul_div_cancel₀ _ h]

theorem reduced_is_reduceElements (x : RationalCoefficients F)
    (hx : 0 ≤ rationalValuation F x) :
    reduceElements F (callPrecision s c t.val) ⟨x,hx⟩ = reduced F t x hx := by
  have h := reduceElements_spec F (callPrecision s c t.val) ⟨x,hx⟩
  rw [reduced_spec F t x hx,Option.some.injEq] at h
  exact h.symm

/-- Identifies the actual packet tensor stored by the source builder
    with local row coefficient extraction in the affine recurrence's
    coefficient ring, at this packet's creation precision. -/
theorem nativeTables_as_packetValue (β : List ℕ) (g : Fin 64) (k : G.Packet) (X : GroupBits F G t g) :
    nativeTables F G cap t j β g k (packetBits F G t (k := k) X) =
      packetValue ((nativeAffineData F G cap t j).localRow g X k)
        (fun z => actualExponent G t β z.val)
        (fun z : SourceAt F G t g k =>
          reduced F t (sourceTile G t (K := RationalCoefficients F) (packetBits F G t (k := k) X) z.val)
            (sourceTile_integral G t (K := RationalCoefficients F) (rationalValuation F)
              (packetBits F G t (k := k) X) z.val))
        (fun z => actualExponent G t β z.val) := by
  have hi := reduceElements_spec F (callPrecision s c t.val) (integralPacket F G cap t j β g k X)
  rw [integralPacket_value, nativeTables_residue, Option.some.injEq] at hi
  rw [hi,integralPacket,map_packetValue]
  congr 1
  · funext x o
    unfold integralRow PacketData.localRow
    rw [map_mul,map_pow,map_ofNat,reduced_is_reduceElements]
  · funext z
    unfold integralRead
    rw [reduced_is_reduceElements]

end RootSeparation.Solver

#print axioms RootSeparation.Solver.integralPacket_value
#print axioms RootSeparation.Solver.nativeTables_as_packetValue
