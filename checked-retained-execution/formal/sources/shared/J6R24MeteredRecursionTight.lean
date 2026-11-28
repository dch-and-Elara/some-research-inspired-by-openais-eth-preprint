import J6R24MeteredRecursionRun
import J6R12IntegralDirectPrinted
import J6R21AncestorWholeEnvelope

/-! The same prepared interpreter can use the canonical sufficient common
scale, without any additional precision supplied by the descriptors.
This prices no producer and proves no unstated uniform tape-length bound. -/
namespace J6R24MeteredRecursion
open scoped Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost J6R21Ancestor
open J6R22Active HermiteLoss

variable {f : ℤ[X]} {ell s C : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {bank : Bank f}

def ActiveDesc.canonical (D : ActiveDesc sel d bank) : ActiveDesc sel d bank :=
  { D with extraPrecision := commonLoss ((S).levelBits c.depth) c.edges ((S).levelWidth c.depth)
           enough := le_rfl }

def Prepared.canonical (T : Prepared cfg sel r hf) : Prepared cfg sel r hf :=
  { T with active := fun c h ha=>(T.active c h ha).canonical }

theorem simple_height_cap {M u : ℕ} (hu : 0<u) (hM : u≤M) : sourceH M u≤4*M := by
  change (3*M+u-1)/u≤4*M
  exact (Nat.div_le_self _ _).trans (by omega)

theorem simple_common_scale_cap {a M u lam : ℕ} (ha : a≤lam)
    (hu : 0<u) (hM : u≤M) :
    commonLoss a M u≤M*(24*2^lam+4*(lam+1)) := by
  unfold commonLoss
  calc
    _≤6*(4*M)*2^lam+(4*M)*(lam+1) := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (simple_height_cap hu hM))
          (Nat.pow_le_pow_right (by decide) ha)
      · exact Nat.mul_le_mul_left _ (Nat.succ_le_succ ha)
    _=_ := by ring

theorem Prepared.canonical_precision (T : Prepared cfg sel r hf)
    (walk : NativeReach (Plan sel) r c) (ha : (S).cutoff<c.edges)
    (h₀ : r.depth=0) (p₀ : r.prec≤C*s) :
    let lam := Nat.clog 2 s
    c.prec+(T.canonical.active c walk ha).extraPrecision≤
      precisionSize s C+(C*s)*(24*2^lam+4*(lam+1)) := by
  have h := stable_reachable cfg sel walk T.rootStable
  have hEdge : c.edges≤C*s := by
    exact (Nat.le_mul_of_pos_left c.edges (Nat.pow_pos (by decide))).trans h.sizeByDepth
  have hPrec := every_call_precision_cap cfg sel r walk T.rootStable h₀ p₀
  have ⟨hu,huM⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ walk ha
  have hA : (S).levelBits c.depth≤Nat.clog 2 s := bits_le_lam _ _
  apply Nat.add_le_add hPrec
  exact (simple_common_scale_cap hA hu huM).trans (Nat.mul_le_mul_right _ hEdge)

#print axioms simple_height_cap
#print axioms simple_common_scale_cap
#print axioms Prepared.canonical_precision
end J6R24MeteredRecursion
