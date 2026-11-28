import V8NativeMessageN5Native

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 4000

/-! Exactly one literal native product of two fixed linear forms.
Only its two entrance rosters and the chosen private points are
counted. The algebraic Cartesian expansion is not metered as an
executed enumeration of cross products. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal J6R9Recursive J6R10Repack N4 V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X] {F : Finset (X×X)}
  {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {d : LayoutReady F reg f} {i : rootKept F f}

abbrev SameCoord (P : RootPacking F reg f) (d : LayoutReady F reg f) (i : rootKept F f) :=
  {s : PublicSlot F reg f P d // atCenter d s.1=i}

def replaceD (q : OrdinaryQuery P d i) (s : SameCoord P d i) : OrdinaryQuery P d i :=
  { q with slot:=s.val,sameCoordinate:=s.property }

variable {I J : Type*} (A : I→OrdinaryQuery P d i) (B : J→SameCoord P d i)

def distributed (h : I×J) : OrdinaryQuery P d i := replaceD (A h.1) (B h.2)

def DForm (s : SameCoord P d i) (hf : f.Monic) (σ : X→Bool) : RatRing f 1 :=
  publicMenuWeight F reg f d s.val.1 s.val.2.1*embed f 1 (rawWhole d hf s.val σ)

theorem distributed_pointwise (hf : f.Monic) (σ : X→Bool) (h : I×J) :
    weightedWhole (distributed A B h) hf σ=ordinaryM (A h.1) σ*DForm (B h.2) hf σ := by
  unfold weightedWhole DForm ordinaryD ordinaryM distributed replaceD
  ring

variable [Fintype I] [Fintype J]

theorem one_fixed_product (hf : f.Monic) (σ : X→Bool) :
    (∑ h : I×J,weightedWhole (distributed A B h) hf σ)=
      (∑ h : I,ordinaryM (A h) σ)*(∑ j : J,DForm (B j) hf σ) := by
  simp only [distributed_pointwise,Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun h _=> (Finset.mul_sum _ _ _).symm)

variable [Fact (Irreducible (ratPoly f))]
  {L : Type*} {width : ℕ} {γ : ℝ} (C : FourCut P i γ) (hf : f.Monic)
  (σ : X→Bool) {t : Trace L (NativePayload f) width}

structure SymbolicReceipts (t : Trace L (NativePayload f) width)
    extends PointReceipts (distributed A B) σ t where
  mainKey : I→L
  mainDistinct : Function.Injective mainKey
  mainDone : ∀ h,Provides t (mainKey h) (Sum.inl (ordinaryM (A h) σ))
  dKey : J→L
  dDistinct : Function.Injective dKey
  dDone : ∀ j,Provides t (dKey j) (Sum.inl (DForm (B j) hf σ))

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem original_symbolic_work_power
    (actual : SymbolicReceipts A B hf σ t)
    (correct : ∀ τ : X→Bool,∃ total : IntRing f 1,
      (∑ h : I,ordinaryM (A h) τ)*(∑ j : J,DForm (B j) hf τ)=embed f 1 total ∧
      reduce (4*Fintype.card X+1) f 1 total=(nativeCount F reg τ:Residue f 1 (4*Fintype.card X+1)))
    {κmax rmax : ℕ} (hk : ∀ h,(A h).order≤κmax) (hr : ∀ h,(A h).groups≤rmax) :
    2^C.m≤κmax*(width*time t)^(rmax+2) := by
  have hc : RightTerminal (distributed A B) hf := by
    intro τ
    obtain ⟨o,ho,hρ⟩ := correct τ
    exact ⟨o,(one_fixed_product A B hf τ).trans ho,hρ⟩
  let M : Roster I t := ⟨actual.mainKey,actual.mainDistinct,
    fun h=>Sum.inl (ordinaryM (A h) σ),actual.mainDone⟩
  let D : Roster J t := ⟨actual.dKey,actual.dDistinct,
    fun j=>Sum.inl (DForm (B j) hf σ),actual.dDone⟩
  exact paid_single_symbolic (H:=I×J) (r:=fun h=>(distributed A B h).groups)
    (κ:=fun h=>(distributed A B h).order) (b:=fun h g=>(distributed A B h).pointList.count g)
    (original_whole_slot_N4 hf C (distributed A B) hc)
    (Function.Embedding.refl (I×J)) M D actual.toPointReceipts.roster
    (fun h=>hk h.1) (fun h=>hr h.1)

#print axioms distributed_pointwise
#print axioms one_fixed_product
#print axioms original_symbolic_work_power
end
end V8NativeMessage.N5