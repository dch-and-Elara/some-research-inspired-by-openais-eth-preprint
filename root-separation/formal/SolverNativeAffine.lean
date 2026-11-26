import SolverAffinePackets
import SolverPacketWords

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial Classical
open scoped BigOperators

variable {e : ℕ} (F : SourcePolynomial e) {s : ℕ} {c : Call F.f}
variable (G : CallLayout s c) (cap : probeCount c.edges (callL s c) ≤ 2^e)
variable (t : callCenters s c) (j : callProbes s c)

abbrev GroupBits (g : Fin 64) := ChildEdge c.network G.left G.right (G.coord t) g → Bool
abbrev LocalRows (g : Fin 64) (k : G.Packet) :=
  {w : PacketPort G t g k // isColumn G t w = false}
abbrev TargetAt (g : Fin 64) (k : G.Packet) :=
  {z : ActualMode G t // z.1.val = k ∧ tileTarget G t z = g}

def unpackActualMode :
    (Σ g : Fin 64, Σ k : G.Packet, TargetAt F G t g k) ≃ ActualMode G t where
  toFun z := z.2.2.val
  invFun z := ⟨tileTarget G t z,z.1.val,z,rfl,rfl⟩
  left_inv := by
    rintro ⟨g,k,z,hk,hg⟩
    subst g
    subst k
    rfl
  right_inv _ := rfl

def packetBits {g : Fin 64} {k : G.Packet} (bits : GroupBits F G t g) (w : PacketPort G t g k) : Bool :=
  bits w.val

def reduced (x : RationalCoefficients F)
    (hx : 0 ≤ rationalValuation F x) : WordRing F.f (callPrecision s c t.val) :=
  integralWord F.f (callPrecision s c t.val)
    (Classical.choose ((coordinateOrder_nonnegative F.monic F.degree x).1 hx))

theorem reduced_spec (x : RationalCoefficients F) (hx : 0 ≤ rationalValuation F x) :
    tryWord F.monic (callPrecision s c t.val) x = some (reduced F t x hx) := by
  unfold tryWord reduced
  rw [dif_pos ((coordinateOrder_nonnegative F.monic F.degree x).1 hx)]

def normalizedEntry {g : Fin 64} {k : G.Packet}
    (bits : GroupBits F G t g) (x : LocalRows F G t g k) :
    Option (TargetAt F G t g k) → RationalCoefficients F
  | none =>
    let q := localForm G t (callPoint F cap j) (packetBits F G t bits) x
    if packetBits F G t bits x.val then q else 1-q
  | some z =>
    let q := crossingCoeff G t (callPoint F cap j) x z.val /
      (2:RationalCoefficients F)^(z.val.2.2.val+1)
    if packetBits F G t bits x.val then q else -q

theorem normalizedEntry_integral {g : Fin 64} {k : G.Packet}
    (bits : GroupBits F G t g) (x : LocalRows F G t g k) (o : Option (TargetAt F G t g k)) :
    0 ≤ rationalValuation F (normalizedEntry F G cap t j bits x o) := by
  let K := RationalCoefficients F
  let v : AddValuation K (WithTop ℤ) := rationalValuation F
  let ζ := callPoint F cap j
  have h₂ : v 2 = 1 := rationalValuation_two F
  have hζ : 0 ≤ v ζ := rationalValuation_integer F _
  cases o with
  | none =>
    simp only [normalizedEntry]
    have h := localForm_integral G t v h₂ ζ hζ (packetBits F G t bits) x
    split
    · exact h
    · change 0 ≤ v (1-localForm G t ζ (packetBits F G t bits) x)
      rw [sub_eq_add_neg]
      apply (le_min (by simp) ?_).trans (v.map_add _ _)
      rw [v.map_neg]
      exact h
  | some z =>
    simp only [normalizedEntry]
    obtain ⟨q,hq,he⟩ := crossingCoeff_factor G t v h₂ ζ hζ x z.val z.property.1 z.property.2
    have hdiv : 0 ≤ v (crossingCoeff G t ζ x z.val / (2:K)^(z.val.2.2.val+1)) := by
      rw [he,mul_div_cancel_left₀ _ (pow_ne_zero _ (NeZero.ne 2))]
      exact hq
    split
    · exact hdiv
    · change 0 ≤ v (- (crossingCoeff G t ζ x z.val / (2:K)^(z.val.2.2.val+1)))
      rwa [v.map_neg]

/-- The concrete packet data accepted by the previously verified S11
    affine recurrence. Both the old group tensors and the mode/tile
    coefficients are evaluated at this probe's printed precision. -/
abbrev nativeAffineData : PacketData (Fin 64) (WordRing F.f (callPrecision s c t.val)) G.Packet where
  Bits := GroupBits F G t
  Rows := LocalRows F G t
  Modes := TargetAt F G t
  source := fun z => tileSource G t z.2.2.val
  weight := fun z => z.2.2.val.2.2.val+1
  old := fun g bits =>
    ∏ v : RetainedOld c.network G.left G.right (G.coord t) g,
      oldTable c.network G.left G.right (G.coord t) g
        (fromInteger F.f (callPrecision s c t.val)) v (fun w => bits w.val)
  normalized := fun _g bits _k x o =>
    reduced F t (normalizedEntry F G cap t j bits x o)
      (normalizedEntry_integral F G cap t j bits x o)
  readTile := fun z bits =>
    reduced F t (sourceTile G t (packetBits F G t (k := z.2.1) bits) z.2.2.val)
      (sourceTile_integral G t (K := RationalCoefficients F) (rationalValuation F)
        (packetBits F G t (k := z.2.1) bits) z.2.2.val)

theorem nativeAffine_weights (z : (nativeAffineData F G cap t j).affine.Z) :
    (nativeAffineData F G cap t j).affine.weight z = (unpackActualMode F G t z).2.2.val+1 := rfl

end RootSeparation.Solver

#print axioms RootSeparation.Solver.nativeAffineData
#print axioms RootSeparation.Solver.nativeAffine_weights
