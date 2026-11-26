import P5AlwaysSatOriginalTaylorFinite
import P5AlwaysSatOriginalTaylorFiniteSparse
import P5MainBalanceM6Variants

/-! The already checked true-row tail and asymptotic arithmetic apply
uniformly at genuine width three. The published N/sqrt(Q) and
N/(sqrt(Q) log(2Q)) scales need no new experimental estimate. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6 Filter Real Polynomial
open scoped Classical BigOperators Polynomial

universe u v

set_option maxHeartbeats 16000000 in
theorem eventual_width_three_M7 (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∃ ε : ℝ, 0<ε ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {V : Type u} {CopyD : Type v} {CopyS : Type v}
        [Fintype V] [DecidableEq V] [Nonempty V] [Fintype CopyD] [Fintype CopyS],
      ∀ (E : Finset (V×V)) (T : Finset V)
        (_reg : ∀ x,GraphCutMoments.degree E x=3)
        (ld : SourceLayout (ClausePort E T) (Port E T) (CloneFactor E T)
          CopyD (Fin (mainNodes n)) (Fin (mainAlphabet n)))
        (hoD : ld.placement.owner=portOwner E T) (hfD : ld.factor=portFactor E T)
        (ls : SourceLayout (SparsePort E T) (Port E T) (SparseFactor E T)
          CopyS (Fin (mainNodes n)) (Fin (mainAlphabet n)))
        (hoS : ls.placement.owner=sparseOwner E T) (hfS : ls.factor=sparseFactor E T),
        mainN E T=n → 8≤Fintype.card V → T.card≤Fintype.card V/4 →
        PrintedCaps n E ld γ → PrintedCaps n E ls γ →
        PrintedWitness n 54 (directDegree E T) 1 γ ε ld (directChart ld hoD hfD).mark
            (directRecipe ld hoD hfD) ∧
          PrintedWitness n 54 (sparseDegree E T) (n+1) γ ε ls (sparseChart ls hoS hfS).mark
            ((sparseInput ls hoS hfS).compile (n+1)) := by
  obtain ⟨ε,hε,hev⟩ := eventual_printed_M6_without_tail 9 54 12 (by decide) (by decide) γ hγ hγ1
  refine ⟨ε,hε,?_⟩
  filter_upwards [hev] with n hn
  intro V CopyD CopyS _ _ _ _ _ E T reg ld hoD hfD ls hoS hfS hn' hN hT capD capS
  have hRange := literal_clone_variable_range E T reg hT
  rw [hn'] at hRange
  have hPorts := main_and_sparse_port_caps E T reg hT hN
  letI : Nonempty (Port E T) := ⟨bonusZeroPort E T⟩
  let md : Mix CopyD (Fin (mainNodes n)) (Fin (mainAlphabet n)) :=
    printedMix (printedStart n) (mainWidth 1 n)
  let ms : Mix CopyS (Fin (mainNodes n)) (Fin (mainAlphabet n)) :=
    printedMix (printedStart n) (mainWidth 1 n)
  constructor
  · have hNom : (∑ f,directBase ld hoD hfD f)+0*(1-1)=directDegree E T := by
      rw [zero_mul,add_zero,direct_nominal]
      rfl
    have hDegree : (∑ f,directBase ld hoD hfD f)+0*(1-1)≤12*n := by
      rw [hNom,actual_direct_degree,hn']
      omega
    obtain ⟨out,hOut,hMod⟩ := direct_terminal_witness ld hoD hfD (nativeGrid n) md
    have cert := hn E ld (directChart ld hoD hfD).mark (directRecipe ld hoD hfD)
      (directBase ld hoD hfD) 0 1 hn' hRange.1 hRange.2 hPorts.1
      capD.cell capD.copies capD.loopless reg capD.expansion
      (direct_grade ld hoD hfD) hDegree (by omega) out hOut hMod
    unfold PrintedWitness
    rw [hNom] at cert
    exact cert
  · have hNom : (∑ f,(sparseInput ls hoS hfS).base f)+6*((n+1)-1)=sparseDegree E T := by
      rw [sparse_nominal_base,show (n+1)-1=n by omega]
      unfold sparseDegree
      rw [hn']
    have hDegree : (∑ f,(sparseInput ls hoS hfS).base f)+6*((n+1)-1)≤12*n := by
      rw [hNom,←hn']
      exact sparse_nominal_width_bound E T
    obtain ⟨out,hOut,hMod⟩ := sparse_terminal_witness ls hoS hfS (n+1)
      (Nat.succ_pos _) (nativeGrid n) ms
    have cert := hn E ls (sparseChart ls hoS hfS).mark ((sparseInput ls hoS hfS).compile (n+1))
      (sparseInput ls hoS hfS).base 6 (n+1) hn' hRange.1 hRange.2 hPorts.2
      capS.cell capS.copies capS.loopless reg capS.expansion
      ((sparseInput ls hoS hfS).graded _) hDegree le_rfl out hOut hMod
    unfold PrintedWitness
    rw [hNom] at cert
    exact cert

#print axioms eventual_width_three_M7
end Paper5.AlwaysSatOriginal.Physical.Taylor