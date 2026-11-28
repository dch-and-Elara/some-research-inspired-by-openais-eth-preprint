import J7R43LiteralPostprocessPhysical

/-! Actual source/zero-child operand width and the verified interpolation
stencil words. This charges postprocessing arithmetic after the finite
register read and public bounded table evaluation; it is not a raw
record or arbitrary-probe acquisition bound. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial J6R9Recursive J8Physical J8J9Grouped
open J9R19CompiledBits
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7800000

private theorem nonnegative_fit (z : ℤ) (w : ℕ)
    (h : 0≤z ∧ z≤(2:ℤ)^w) : Fits w z := by
  cases z with
  | ofNat k =>
    change k≤(2:ℕ)^w
    have hk : (↑k : ℤ) ≤ (2:ℤ)^w := h.2
    exact_mod_cast hk
  | negSucc k => omega

variable {Packet R S V G : Type} {P : V→Type} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
variable (e : EndpointSeating d) (even : Even L)
variable (F : OldTables d) (sign : S→Bool)
variable {f : ℤ[X]} {ell : ℕ}
variable (s : S) (p : ℕ) (hf : f.Monic) (hell : 0<ell)
variable (base : Box f ell p) (obs : Fin (Fintype.card (PinTile d s))→Box f ell p)

theorem named_amplitude_operands (L : ℕ) (hL : 1≤L) :
    (kernelRun L).coeff=J9FactorBounds.kernel L ∧
    (kernelRun L).work≤(2*L-1)*(2*L)+1 ∧
    Fits (2*L) (kernelRun L).coeff ∧ (∀ z∈(kernelRun L).oldRows,z≤2^(2*L)) :=
  ⟨kernelRun_exact L,kernelRun_work L,(kernelRun_width L hL).1,(kernelRun_width L hL).2⟩

theorem source_coordinate_power_operands (w : Wire R) (n : ℕ) :
    let r := powerRun (ordinal d w:ℤ) n
    r.value=(ordinal d w:ℤ)^n ∧ r.work=n ∧ (∀ x∈r.writes,Fits (L*n) x) :=
  ⟨(powerRun_exact _ _).1,(powerRun_exact _ _).2,powerRun_width _ (ordinal_fits d w) n⟩

theorem original_J7_decoder_word_bound
    (idx : Wire R≃Fin M) (hL : 3≤L) (hM : L^3≤M)
    (capacity : L*Fintype.card Packet≤3*M)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x=true)
    (hp : 10*M≤p) (hF : 0<f.natDegree)
    (hbase : base = (J8J9Grouped.child d e even F sign (d.pinLabel s) none (fun _ => 1) : Box f ell p))
    (hobs : ∀ b, obs b = (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) : Box f ell p))
    (j : Fin (Fintype.card (PinTile d s))) :
    let Z := (readUnsigned p hf hell base : ℤ)
    let bg := fun b : Fin (Fintype.card (PinTile d s)) => publicBackgroundInteger d e even F s b.val
    let moments := fun b => (readUnsigned p hf hell (obs b) : ℤ)
    let N := normalTape (literalDecoderInput Z bg moments)
    let st := evaluateStencil (coordinateInt d s) (fun b => storedFraction N b.val) j
    (∀ r∈N, ∀ x∈r.words,Fits (3*(8*M)+1) x) ∧
    st.result.fits (decoderBudget (Fintype.card (PinTile d s)) L (8*M)) ∧
    (∀ x∈st.words,Fits (decoderBudget (Fintype.card (PinTile d s)) L (8*M)) x) := by
  dsimp only
  have hm : 0<M := (pow_pos (by omega : 0<L) 3).trans_le hM
  have hR := literal_native_baseline_fits d e even F sign s idx (by omega) hm capacity (d.pinLabel s) p hp
  have hBase : Fits (8*M) (readUnsigned p hf hell base : ℤ) := by
    rw [hbase,readUnsigned_exact_int p (by omega) hf hF hell _ hR.1 hR.2]
    exact nonnegative_fit _ _ (literal_group_feature_range d e even F sign s idx (by omega)
      capacity (d.pinLabel s) _ (fun _ => ⟨by norm_num,one_le_pow₀ (by norm_num)⟩))
  have hBg (b : Fin (Fintype.card (PinTile d s))) :
      Fits (8*M) (publicBackgroundInteger d e even F s b.val) := by
    unfold publicBackgroundInteger
    rw [← literal_source_no_division d e even (by omega) F (fun _=>false) s b sat]
    exact nonnegative_fit _ _ (literal_group_feature_range d e even F (fun _=>false) s idx (by omega)
      capacity _ (feature d s b) (source_feature_range d even s idx hL hM b))
  have hObs (b : Fin (Fintype.card (PinTile d s))) :
      Fits (8*M) (readUnsigned p hf hell (obs b) : ℤ) := by
    have hb := literal_native_source_fits d e even F sign s idx hL hM capacity b p hp
    rw [hobs b,readUnsigned_exact_int p (by omega) hf hF hell _ hb.1 hb.2]
    exact nonnegative_fit _ _ (literal_group_feature_range d e even F sign s idx (by omega) capacity _
      (feature d s b) (source_feature_range d even s idx hL hM b))
  exact literal_decoder_machine_words (coordinateInt d s) _ _ _ j
    (coordinateInt_fits d s) hBase hBg hObs

#print axioms named_amplitude_operands
#print axioms source_coordinate_power_operands
#print axioms original_J7_decoder_word_bound
end
end J7R43Literal
