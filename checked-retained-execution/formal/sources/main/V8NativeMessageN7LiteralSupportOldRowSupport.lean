import V8NativeMessageN7LiteralSupportOldGateAssembly
import V8NativeMessageN7LiteralSupportOddSign
import V8NativeMessageN7LiteralSupportZero

/-! Real old-row support, not the parity support: it is empty when a
positive OR has no real shifted port, and otherwise exactly the subcube
requiring unmatched unary pins to carry the zero sign. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P1DyadicGrid P1DyadicGridBridge P11FullPacking J6R10Repack J6R9PacketTiles DenominatorBudget
open Paper5.HybridClosure Paper5.D1Literal J6R9PacketCoeff
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000
set_option maxRecDepth 2500
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {a : ℕ}
local notation "E" => (DWire F)
local notation "N" => (dNetwork F reg)
variable (P : PhysicalPacking (dNetwork F reg) a (Fin 64))
local notation "rArg" => (coefficientAt («E»:=DWire F) (A:=DOld F) (B:=MainClonedCNF.Port F) (G:=Fin 64) (R:=ℚ) (n:=a) («N»:=dNetwork F reg))

def shiftPresent (t : ℤ) (r : E) : Prop := ∃ q,Matches P t r q

def oldRowSupported (t : ℤ) (σ : W→Bool) : Prop :=
  (∀ e : F,∃ b : Bool,shiftPresent F reg P t (.inr (.inl (e,b)),true)) ∧
  (∀ v : W,σ v=true→shiftPresent F reg P t (.inl v,true))

private theorem actual_read_imp_match {t : ℤ} {r : E} {y : E→Bool}
    (active : readTrueShift P t r y=true) : shiftPresent F reg P t r := by
  unfold readTrueShift at active
  split at active
  · rename_i found
    exact found
  · cases active

private theorem all_one_actual_read {t : ℤ} {r : E} (present : shiftPresent F reg P t r) :
    readTrueShift P t r (fun _=>true)=true := by
  unfold readTrueShift
  rw [dif_pos (show ∃ q,Matches P t r q from present)]

private theorem argument_as_shift (t : ℤ) (κ : ℚ) (y : E→Bool) (r : E) :
    rArg P t κ y r=shiftArg κ (readTrueShift P t r y) := by
  rw [coefficientAt,shifted_bits_are_exact_boolean]
  cases readTrueShift P t r y <;> simp [shiftArg,bit]

private theorem argument_nonpos (t : ℤ) {κ : ℚ} (neg : κ<0) (y : E→Bool) (r : E) :
    rArg P t κ y r≤0 := by
  rw [argument_as_shift]
  cases readTrueShift P t r y <;> simp [shiftArg,neg.le]

def rowPhase (σ : W→Bool) : DOld F→ℚ
  | .inl _ => 1
  | .inr (.inl v) => if σ v then -1 else 1
  | .inr (.inr (.inl _)) => -1
  | .inr (.inr (.inr _)) => 1

private theorem clone_always_positive (t : ℤ) {κ : ℚ} (neg : κ<0) (σ : W→Bool)
    (y : E→Bool) (v : Clone W) :
    0<literalRowFactor F reg σ (rArg P t κ y) (.inl v) := by
  rw [original_clone_eval]
  let I := LiteralRowScope F reg (.inl v)
  letI : Nonempty I := Fintype.card_pos_iff.mp (by
    change 0<Fintype.card (LiteralRowScope F reg (.inl v))
    rw [actual_clone_scope_card]; omega)
  exact equality_active_factor_positive (fun r : I=>rArg P t κ y r.val)
    (fun r=>argument_nonpos F reg P t neg y r.val)

private theorem imp_always_positive (t : ℤ) {κ : ℚ} (neg : κ<0) (σ : W→Bool)
    (y : E→Bool) (v : W) (j : Fin 4) :
    0<literalRowFactor F reg σ (rArg P t κ y) (.inr (.inr (.inr (v,j)))) := by
  rw [original_imp_eval]
  exact actual_implication_positive (argument_nonpos F reg P t neg y _) (argument_nonpos F reg P t neg y _)

private theorem real_row_common_phase (t : ℤ) {κ : ℚ} (neg : κ<0) (σ : W→Bool)
    (u : DOld F) (y : E→Bool) :
    0≤rowPhase F σ u*literalRowFactor F reg σ (rArg P t κ y) u := by
  rcases u with v|(v|e|⟨v,j⟩)
  · simpa only [rowPhase,one_mul] using (clone_always_positive F reg P t neg σ y v).le
  · rw [original_pin_eval,argument_as_shift]
    cases b : σ v
    · simpa only [rowPhase,b,Bool.false_eq_true,if_false,one_mul,pinEval] using
        (actual_unary_shift_support neg (readTrueShift P t (.inl v,true) y)).1.le
    · simpa only [rowPhase,b,if_true,neg_one_mul] using
        neg_nonneg.mpr (actual_unary_shift_support neg (readTrueShift P t (.inl v,true) y)).2.1
  · rw [original_or_eval,argument_as_shift,argument_as_shift]
    simpa only [rowPhase,neg_one_mul,clauseOr] using neg_nonneg.mpr
      (actual_or_shift_support neg (readTrueShift P t (.inr (.inl (e,false)),true) y)
        (readTrueShift P t (.inr (.inl (e,true)),true) y)).1
  · simpa only [rowPhase,one_mul] using (imp_always_positive F reg P t neg σ y v j).le

theorem actual_old_row_rational_support (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) {κ : ℚ} (neg : κ<0) (σ : W→Bool) :
    signedRoot P i t κ (oldRowTruth F reg σ)≠0 ↔ oldRowSupported F reg P t σ := by
  rw [actual_old_rows_summed F reg P i ht hv κ σ]
  have phaseUnit (u : DOld F) : rowPhase F σ u=1 ∨ rowPhase F σ u= -1 := by
    rcases u with v|(v|e|q)
    · exact Or.inl rfl
    · cases b : σ v <;> simp [rowPhase,b]
    · exact Or.inr rfl
    · exact Or.inl rfl
  have main := common_phase_support (keepsSubdivision F)
    (fun u y=>literalRowFactor F reg σ (rArg P t κ y) u)
    (rowPhase F σ) phaseUnit (real_row_common_phase F reg P t neg σ)
  change signedSum (keepsSubdivision F)
    (fun u y=>literalRowFactor F reg σ (rArg P t κ y) u)≠0 ↔ _
  rw [main]
  constructor
  · rintro ⟨y,_,active⟩
    constructor
    · intro e
      have p := active (.inr (.inr (.inl e)))
      change literalRowFactor F reg σ (rArg P t κ y) (.inr (.inr (.inl e)))≠0 at p
      rw [original_or_eval,argument_as_shift,argument_as_shift] at p
      have h := (actual_or_shift_support neg
        (readTrueShift P t (.inr (.inl (e,false)),true) y)
        (readTrueShift P t (.inr (.inl (e,true)),true) y)).2.mp p
      exact h.elim (fun z=>⟨false,actual_read_imp_match F reg P z⟩)
        (fun z=>⟨true,actual_read_imp_match F reg P z⟩)
    · intro v hv'
      have p := active (.inr (.inl v))
      change literalRowFactor F reg σ (rArg P t κ y) (.inr (.inl v))≠0 at p
      rw [original_pin_eval,argument_as_shift,hv'] at p
      exact actual_read_imp_match F reg P ((actual_unary_shift_support neg
        (readTrueShift P t (.inl v,true) y)).2.2.mp p)
  · rintro ⟨ors,pins⟩
    refine ⟨fun _=>true,all_one_subdivision_columns F,?_⟩
    intro u
    rcases u with v|(v|e|⟨v,j⟩)
    · exact (clone_always_positive F reg P t neg σ _ v).ne'
    · change literalRowFactor F reg σ (rArg P t κ (fun _=>true)) (.inr (.inl v))≠0
      rw [original_pin_eval,argument_as_shift]
      cases c : σ v
      · exact (actual_unary_shift_support neg (readTrueShift P t (.inl v,true) (fun _=>true))).1.ne'
      · exact (actual_unary_shift_support neg (readTrueShift P t (.inl v,true) (fun _=>true))).2.2.mpr
          (all_one_actual_read F reg P (pins v c))
    · change literalRowFactor F reg σ (rArg P t κ (fun _=>true)) (.inr (.inr (.inl e)))≠0
      rw [original_or_eval,argument_as_shift,argument_as_shift]
      apply (actual_or_shift_support neg _ _).2.mpr
      obtain ⟨b,h⟩ := ors e
      cases b
      · exact Or.inl (all_one_actual_read F reg P h)
      · exact Or.inr (all_one_actual_read F reg P h)
    · exact (imp_always_positive F reg P t neg σ _ v j).ne'

theorem actual_old_row_odd_exact_support (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (mem : t∈grid a) (odd : Odd t)
    (σ : W→Bool) :
    exactZero P i t (oldRowTruth F reg σ)≠0 ↔ oldRowSupported F reg P t σ := by
  have map : twoLocalRat (exactZero P i t (oldRowTruth F reg σ)) =
      signedRoot P i t (derivRatio a t:ℚ) (oldRowTruth F reg σ) := by
    rw [exactZero,full_signed_root_is_zero_polynomial,map_signed_root,rho_rat mem]
  have faith : exactZero P i t (oldRowTruth F reg σ)=0 ↔
      twoLocalRat (exactZero P i t (oldRowTruth F reg σ))=0 := by
    constructor
    · intro h; rw [h,map_zero]
    · intro h; apply twoLocalRat_injective; simpa only [map_zero] using h
  have mapped : twoLocalRat (exactZero P i t (oldRowTruth F reg σ))≠0 ↔ oldRowSupported F reg P t σ := by
    rw [map]
    exact actual_old_row_rational_support F reg P i ht hv (odd_centres_have_negative_actual_scalar mem odd) σ
  exact (not_congr faith).trans mapped

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_old_row_rational_support
#print axioms V8NativeMessage.N7LiteralSupport.actual_old_row_odd_exact_support
