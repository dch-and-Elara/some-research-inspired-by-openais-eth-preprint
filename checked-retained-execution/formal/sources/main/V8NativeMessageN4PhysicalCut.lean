import V8NativeMessageN4PhysicalDensity
import V8NativeMessageC2PhysicalCut

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000

/-! The N4 matching itself uses the four-copy old-row D1 layout.
Only the already audited generic cubic greedy lemma is reused from
C2; no C2 parity chart, pinned switches, or five-copy file is used. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open V8PooledRange V8NativeMessage.C2Physical
open Paper5.HybridClosure Paper5.D1Literal J6R12Blueprint J6R10Repack J1PPrinted
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
variable {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}

def storageGraph (F : Finset (W×W)) : Graph W F :=
  fun e b => if b then e.val.2 else e.val.1

omit [Fintype W] in
theorem base_exterior (q : F×Bool) :
    (exteriorPort F reg q).1=storageGraph F q.1 q.2 := by
  obtain ⟨e,b⟩ := q
  cases b <;> rfl

def trueGraphPorts (reg : ∀ v, GraphCutMoments.degree F v=3) : ThreePorts (storageGraph F) :=
  fun v =>
    { toFun := fun a => (exteriorPort F reg a.val).2
      invFun := fun k => ⟨(exteriorPort F reg).symm (v,k),by
        rw [← base_exterior (reg:=reg),Equiv.apply_symm_apply]⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply (exteriorPort F reg).injective
        rw [Equiv.apply_symm_apply]
        apply Prod.ext
        · exact ((base_exterior (reg:=reg) a.val).trans a.property).symm
        · rfl
      right_inv := fun k => by
        dsimp only
        rw [Equiv.apply_symm_apply] }

omit [Fintype W] [DecidableEq W] in
theorem storage_loopless (hloop : ∀ v, (v,v)∉F) :
    ∀ e, storageGraph F e false≠storageGraph F e true := by
  rintro ⟨⟨v,w⟩,h⟩ eq
  change v=w at eq
  subst w
  exact hloop v h

local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => oldRowRoot F reg f (fun _=>false)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

structure FourCut (P : RootPacking F reg f) (i : rootKept F f) (γ : K) where
  T : Finset (Fin 64)
  m : ℕ
  pairs : Pairs (storageGraph F) m
  left : ∀ j, pinGroup P i (pairs.seat (j,false))∈T
  right : ∀ j, pinGroup P i (pairs.seat (j,true))∉T
  balanced : Fintype.card W≤4*min (switchUnion P i T).card
    (Fintype.card W-(switchUnion P i T).card)
  boundary_budget : (boundary (storageGraph F) (switchUnion P i T)).card≤17*m
  match_budget : γ*(Fintype.card W:K)≤68*(m:K)

theorem four_cut_from_pack (P : RootPacking F reg f) (d : Ready S Δ r*)
    (hv : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*Δ)
    (i : rootKept F f) (γ : K) (hγ : 0≤γ) (hE : ExpansionOn (storageGraph F) γ)
    (hloop : ∀ v, (v,v)∉F) : Nonempty (FourCut P i γ) := by
  obtain ⟨T,bal⟩ := original_balanced_union P d hv i
  let A₀ := switchUnion P i T
  let b := min A₀.card (Fintype.card W-A₀.card)
  obtain ⟨m,K₀,hc,hl,hr⟩ := crossing_pairs (storageGraph F) A₀ (storage_loopless hloop) (trueGraphPorts reg)
  have hb : (Fintype.card W:K)≤4*(b:K) := by exact_mod_cast bal
  have he : γ*(b:K)≤((boundary (storageGraph F) A₀).card:K) := hE A₀
  have hcap : ((boundary (storageGraph F) A₀).card:K)≤17*(m:K) := by exact_mod_cast hc
  have hbudget : γ*(Fintype.card W:K)≤68*(m:K) := by
    calc
      _ ≤ γ*(4*(b:K)) := mul_le_mul_of_nonneg_left hb hγ
      _ = 4*(γ*(b:K)) := by ring
      _ ≤ 4*((boundary (storageGraph F) A₀).card:K) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ ≤ 4*(17*(m:K)) := mul_le_mul_of_nonneg_left hcap (by norm_num)
      _ = _ := by ring
  exact ⟨⟨T,m,K₀,fun j => (mem_switch_union P i T _).mp (hl j),
    fun j hj => hr j ((mem_switch_union P i T _).mpr hj),bal,hc,hbudget⟩⟩

def atCenter (d : Ready S Δ r*) (t : PublicCenter F reg f) : rootKept F f :=
  ⟨PublicIndex F reg f d t,publicIndex_mem F reg f d t⟩

/-- A selected actual nonzero D center recovers its own coordinate,
not an unrelated layout or newly drawn coloring. -/
theorem four_cut_at_literal_center (P : RootPacking F reg f) (d : Ready S Δ r*)
    (hv : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*Δ)
    (t : PublicCenter F reg f) (γ : K) (hγ : 0≤γ)
    (hE : ExpansionOn (storageGraph F) γ) (hloop : ∀ v, (v,v)∉F) :
    Nonempty (FourCut P (atCenter d t) γ) :=
  four_cut_from_pack P d hv (atCenter d t) γ hγ hE hloop

#print axioms base_exterior
#print axioms trueGraphPorts
#print axioms storage_loopless
#print axioms four_cut_from_pack
#print axioms four_cut_at_literal_center
end
end V8NativeMessage.N4
