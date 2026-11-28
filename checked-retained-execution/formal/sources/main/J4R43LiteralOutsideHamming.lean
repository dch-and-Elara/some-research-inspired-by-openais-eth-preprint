import J4R43LiteralOutsideValue

/-! The nonconstant factor is composed only from the true unary
pin columns that are reached by the same physical shift. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4400000

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ} {R : Type} [CommRing R]
local notation "E" => DWire F
local notation "N" => oldColumnNetwork F reg
variable (P : PhysicalPacking N a (Fin 64))

def literalPin : W→E := fun v=>(.inl v,true)
def pinColumn : W→DOld F := fun v=>.inr (.inl v)

def pinArgument (v : W) : ColumnArgs F reg (pinColumn F v) :=
  ⟨.inr (literalPin F v),rfl⟩

theorem only_literal_pin_argument (v : W) (p : ColumnArgs F reg (pinColumn F v)) :
    p=pinArgument F reg v := by
  rcases p with ⟨p,h⟩
  cases p with
  | inl d => exact nomatch h
  | inr d =>
    obtain ⟨q,b⟩ := d
    cases b
    · change Sum.inr (Sum.inl (cloneOwner F reg q)) = _ at h
      exact nomatch h
    · rcases q with w|(e|j)
      · have hw : w=v := by
          have k := Sum.inr.inj h
          exact Sum.inl.inj (Sum.inr.inj k)
        subst w
        rfl
      · exact nomatch h
      · exact nomatch h

theorem pin_argument_weight (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) (v : W) :
    localColumnValue F reg P t κ σ (pinColumn F v) =
      if columnHit P t (literalPin F v) ∧ σ v=true then 1-κ else 1 := by
  let p := pinArgument F reg v
  let X : ColumnArgs F reg (pinColumn F v)→Bool := fun _=>σ v
  have truth (x : ColumnArgs F reg (pinColumn F v)→Bool) :
      oldColumnTruth F reg σ (.inr (pinColumn F v)) x=decide (x p=σ v) :=
    unary_column_literal F reg σ v x
  unfold localColumnValue
  rw [Finset.sum_eq_single X]
  · unfold localColumnTerm
    rw [truth]
    have H : X p=σ v := rfl
    change bit R (decide (X p=σ v))*_ =_
    rw [H]
    simp only [decide_true,bit,if_true,one_mul]
    rw [Finset.prod_eq_single p]
    · change (if columnHit P t (literalPin F v) then 1-κ*bit R (σ v) else 1)=_
      cases b : σ v <;> simp [b,bit]
    · intro q _ hq
      exact (hq (only_literal_pin_argument F reg v q)).elim
    · simp
  · intro x _ h
    unfold localColumnTerm
    rw [truth]
    have e : x p≠σ v := by
      intro hp
      apply h
      funext q
      rw [only_literal_pin_argument F reg v q]
      exact hp
    change bit R (decide (x p=σ v))*_ =0
    simp [e,bit]
  · simp

def hitPins (P : PhysicalPacking N a (Fin 64)) (t : ℤ) : Finset W :=
  Finset.univ.filter fun v=>columnHit P t (literalPin F v)

def hitWeight (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (σ : W→Bool) : ℕ :=
  ((hitPins F reg P t).filter (fun v=>σ v=true)).card

def graphFactor (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) : R :=
  (∏ b : Clone W,localColumnValue F reg P t κ (fun _=>false) (.inl b)) *
  ∏ b : ↥F⊕Clone W,localColumnValue F reg P t κ (fun _=>false) (.inr (.inr b))

theorem true_clone_marginal_constant (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ τ : W→Bool) (b : Clone W) :
    localColumnValue F reg P t κ σ (.inl b)=localColumnValue F reg P t κ τ (.inl b) := rfl

theorem true_binary_marginal_constant (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ τ : W→Bool) (b : ↥F⊕Clone W) :
    localColumnValue F reg P t κ σ (.inr (.inr b))=
    localColumnValue F reg P t κ τ (.inr (.inr b)) := by cases b <;> rfl

theorem literal_hamming_factorization (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : R) (σ : W→Bool) :
    factorizedValue F reg P t κ σ =
      graphFactor F reg P t κ*(1-κ)^hitWeight F reg P t σ := by
  let h := fun u : DOld F=>localColumnValue F reg P t κ σ u
  unfold factorizedValue graphFactor
  change (∏ u,h u) =_
  rw [Fintype.prod_sum_type h,Fintype.prod_sum_type (fun b=>h (.inr b))]
  have L :
      (∏ b : Clone W,h (.inl b)) =
      ∏ b : Clone W,localColumnValue F reg P t κ (fun _=>false) (.inl b) :=
    Finset.prod_congr rfl (fun b _=>true_clone_marginal_constant F reg P t κ σ _ b)
  have U : (∏ b : ↥F⊕Clone W,h (.inr (.inr b))) =
      ∏ b : ↥F⊕Clone W,localColumnValue F reg P t κ (fun _=>false) (.inr (.inr b)) :=
    Finset.prod_congr rfl (fun b _=>true_binary_marginal_constant F reg P t κ σ _ b)
  have M : (∏ b : W,h (.inr (.inl b)))=(1-κ)^hitWeight F reg P t σ := by
    let φ := fun v : W=>columnHit P t (literalPin F v) ∧ σ v=true
    have heq : ((hitPins F reg P t).filter (fun v=>σ v=true)) = Finset.univ.filter φ := by
      ext v
      simp [hitPins,φ]
    calc
      _ = ∏ b : W,if φ b then 1-κ else 1 := by
        refine Finset.prod_congr rfl (fun b _=>?_ )
        exact pin_argument_weight F reg P t κ σ b
      _ = ∏ _b ∈ Finset.univ.filter φ, (1-κ) :=
        (Finset.prod_filter φ (fun _=>1-κ)).symm
      _ = _ := by rw [Finset.prod_const, hitWeight,heq]
  rw [L,M,U]
  ac_rfl

theorem last_pin_makes_set_nonempty (P : PhysicalPacking N a (Fin 64)) {h : ℕ} (G : BandCertificate P h)
    (v : W) (last : (P.seat (literalPin F v)).2.val+1=2^a) :
    v∈hitPins F reg P (((2^a:ℕ):ℤ)-1) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,last_seat_is_matched P G (literalPin F v) last⟩

theorem hamming_le_selected (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (σ : W→Bool) :
    hitWeight F reg P t σ≤(hitPins F reg P t).card :=
  Finset.card_le_card (Finset.filter_subset ..)

#print axioms only_literal_pin_argument
#print axioms pin_argument_weight
#print axioms true_clone_marginal_constant
#print axioms true_binary_marginal_constant
#print axioms literal_hamming_factorization
#print axioms last_pin_makes_set_nonempty
#print axioms hamming_le_selected
end
end J4R43LiteralOutside

