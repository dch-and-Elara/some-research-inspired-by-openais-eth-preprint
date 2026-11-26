import P5HybridDUnclonedCount
import P5HybridDUnclonedDegree
import P5HybridDUnclonedTags
import P5HybridDUnclonedParams
import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 24000000
set_option maxRecDepth 2100

/-! Connect the actual uncloned tensor file to the printed root.
No pre-given value of the contracted network and no supplied numeric
packing feasibility are used for the eventual family. -/
namespace Paper5.HybridDUncloned
open scoped Classical Polynomial BigOperators Topology
open Polynomial J6R10Repack J6R9Recursive J6R11Repack J6R11Blueprint J6ActiveRun
  J6ActiveSchedule J6R12Blueprint J1PPrinted J1MainSourceCollision
  Paper5.HybridClosure J9PrintedSchedule P1DyadicGrid Filter

noncomputable section

section Root
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => network F cubic

def root (f : ℤ[X]) (σ : W→Bool) : Call (PhysicalHost f 1) :=
  ⟨physicalHost N (file F cubic f (Fintype.card W+1) σ),0,
    Fintype.card (Wire F),Fintype.card W+1⟩

omit [Fintype W] [DecidableEq W] in
theorem legal_clause_real_ports (loopless : ∀ v,(v,v)∉F) (e : F) : e.val.1≠e.val.2 := by
  intro h
  have eq : e.val=(e.val.1,e.val.1) := Prod.ext rfl h.symm
  exact loopless e.val.1 (eq ▸ e.property)

theorem root_tags (f : ℤ[X]) (σ : W→Bool) :
    GoodTags (root F cubic f σ).host (root F cubic f σ).prec := by
  intro v
  change Fintype.card W+1≤Fintype.card W+1
  exact le_rfl

theorem root_degrees (f : ℤ[X]) (σ : W→Bool) {Δ : ℕ} (hΔ : 3≤Δ) :
    GoodDegree (root F cubic f σ).host Δ := by
  constructor
  · intro v
    change Nat.card {e : Wire F // (N).row e=v}≤Δ
    let emb : {e : Wire F // (N).row e=v} ↪ ↥(facFibre (N).row v) :=
      ⟨fun x=>⟨x.val,by simp [facFibre,x.property]⟩,
        fun _ _ h=>Subtype.ext (congrArg (fun z : ↥(facFibre (N).row v)=>z.val) h)⟩
    have h : Nat.card {e : Wire F // (N).row e=v}≤(facFibre (N).row v).card := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
        Fintype.card_le_of_injective emb emb.injective
    exact h.trans ((old_degree F cubic v).trans hΔ)
  · intro v
    change Nat.card {e : Wire F // (N).col e=v}≤Δ
    let emb : {e : Wire F // (N).col e=v} ↪ ↥(varFibre (N).col v) :=
      ⟨fun x=>⟨x.val,by simp [varFibre,x.property]⟩,
        fun _ _ h=>Subtype.ext (congrArg (fun z : ↥(varFibre (N).col v)=>z.val) h)⟩
    have h : Nat.card {e : Wire F // (N).col e=v}≤(varFibre (N).col v).card := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using
        Fintype.card_le_of_injective emb emb.injective
    rw [subdivision_degree F cubic v] at h
    omega

theorem root_stable (f : ℤ[X]) (σ : W→Bool) (hΔ : 3≤sourceDelta (sourceSize F)) :
    Stable (sourceSize F) 3 (root F cubic f σ) := by
  refine stable_root _ _ _ rfl rfl (root_degrees F cubic f σ hΔ) (root_tags F cubic f σ) ?_
  exact (literal_size_bounds F cubic).2.2

theorem root_literal_count (f : ℤ[X]) (hf : f.Monic) (σ : W→Bool) :
    let r := root F cubic f σ
    reduce r.prec f 1 (r.host.contract hf) =
      (PinnedCNF.modelCount (PinnedCNF.formula F σ):Residue f 1 r.prec) :=
  literal_contraction_is_uncloned_count F cubic f hf _ σ

variable {f : ℤ[X]}
local notation "SP" => printedParams (f:=f) (ell:=1) (sourceSize F)
local notation "Delta" => sourceDelta (sourceSize F)

omit [DecidableEq W] in
theorem root_config
    (degree : f.natDegree=4*Nat.clog 2 (sourceSize F))
    (large : (2*epsDen)^30*(3:ℕ)^10≤Nat.clog 2 (sourceSize F)) :
    RootBounds (sourceSize F) 3 f := by
  obtain ⟨_,hSize,hWidth⟩ := J6R11Threshold.printed_size_implies_numeric_guards
    (sourceSize F) 3 (by decide) large
  exact ⟨degree,by decide,hSize,hWidth,large⟩

theorem root_ready (σ : W→Bool)
    (degree : f.natDegree=4*Nat.clog 2 (sourceSize F))
    (large : (2*epsDen)^30*(3:ℕ)^10≤Nat.clog 2 (sourceSize F))
    (tune : RootTune (sourceSize F) (Fintype.card (Wire F))) :
    Ready SP Delta (root F cubic f σ) :=
  getReady (root_config F degree large) (root_stable F cubic f σ tune.degree) tune.active

theorem root_literal_center_at_level (σ : W→Bool)
    (d : Ready SP Delta (root F cubic f σ))
    (j : Fin (rootWidth (sourceSize F))) :
    ∃ t : Center SP (root F cubic f σ),(centerIndex d t).val=j.val := by
  let M := Fintype.card (Wire F)
  let a := rootBits (sourceSize F)
  let u := rootWidth (sourceSize F)
  let z := pow₂ j.val
  have posM : 0<M := Nat.zero_lt_of_lt d.active
  have posU : 0<u := Nat.zero_lt_of_lt j.isLt
  have widen : u≤a := by
    have eq : a=2*u := (printed_dimension_words (sourceSize F)).1
    omega
  have hp : 0<height M u := by
    have h : 1≤height M u := (Nat.le_div_iff_mul_le posU).mpr
      (by omega)
    omega
  have val : padicValInt 2 z=j.val := by
    simpa [z] using valuation_pow₂_mul_odd j.val (by decide : Odd (1:ℤ))
  have pin : 0<z := pow₂_pos _
  have top : z<pow₂ a :=
    pow_lt_pow_right₀ (by decide : (1:ℤ)<2) (j.isLt.trans_le widen)
  have hd : z∈grid a := mem_grid.mpr
    ⟨by have pa:=pow₂_pos a; linarith only [pin,pa],top⟩
  have active : z∈J6ActiveSchedule.active a M u := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨pin.ne',hd⟩,?_⟩
    unfold J6ActiveSchedule.order
    rw [val]
    exact Nat.mul_pos hp (Nat.sub_pos_of_lt j.isLt)
  exact ⟨⟨z,active⟩,val⟩

theorem same_uncloned_root_has_two_centers (σ : W→Bool)
    (d : Ready SP Delta (root F cubic f σ))
    (width : 2≤rootWidth (sourceSize F)) :
    ∃ t₀ t₁ : Center SP (root F cubic f σ),
      (centerIndex d t₀).val=0 ∧ (centerIndex d t₁).val=1 ∧ centerIndex d t₀≠centerIndex d t₁ := by
  obtain ⟨t₀,h₀⟩ := root_literal_center_at_level F cubic σ d ⟨0,by omega⟩
  obtain ⟨t₁,h₁⟩ := root_literal_center_at_level F cubic σ d ⟨1,by omega⟩
  refine ⟨t₀,t₁,h₀,h₁,?_⟩
  intro eq
  have hz := congrArg Fin.val eq
  exact (by decide : (0:ℕ)≠1) (h₀.symm.trans (hz.trans h₁))

end Root

#print axioms legal_clause_real_ports
#print axioms root_tags
#print axioms root_degrees
#print axioms root_stable
#print axioms root_literal_count
#print axioms root_config
#print axioms root_ready
#print axioms root_literal_center_at_level
#print axioms same_uncloned_root_has_two_centers
end
end Paper5.HybridDUncloned
