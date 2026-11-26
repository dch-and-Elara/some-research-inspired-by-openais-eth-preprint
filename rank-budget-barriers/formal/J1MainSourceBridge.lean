import J1MainSourceLabels
import J1MainSourcePlacement
import NativeJ2
import Mathlib.Tactic

/-! Wiring the resulting original MAIN layout into the finite NativeJ2
interface. The graph cost estimates and the independent D-side assumptions
remain visible where they are still needed. -/
namespace J1MainSourceBridge
open scoped Polynomial
open MainProbe J1MainSourceLabels J1MainSourcePlacement
universe i s e v f b a
variable {I : Type i} {S : Type s} {E : Type e} {V : Type v}
  {F : Type f} {B : Type b} {A : Type a}

section Placement
variable [Fintype I] [DecidableEq I] [Fintype S] [Fintype E]

/-- Use the actual maximum cell load rather than an independently granted
existence of a copy array. -/
noncomputable def copies (data : IncidenceData I S E V F) : ℕ :=
  Finset.univ.sup fun u : Cell I S => Fintype.card (CellFibre data u)

theorem copies_suffice (data : IncidenceData I S E V F) (u : Cell I S) :
    Fintype.card (CellFibre data u) ≤ copies data := by
  unfold copies
  exact Finset.le_sup (f := fun y : Cell I S => Fintype.card (CellFibre data y)) (Finset.mem_univ u)

theorem copies_budget (data : IncidenceData I S E V F) (h : ℕ)
    (hcap : ∀ u, Fintype.card (CellFibre data u) ≤ h) : copies data ≤ h := by
  exact Finset.sup_le (fun u _ => hcap u)

noncomputable def compiledLayout [Fintype A] (data : IncidenceData I S E V F) (pin : A → E) :
    DiagonalLayout I S V (Fin (copies data)) (Fin (Fintype.card (Diagonal data pin))) :=
  enumerateLayout data (copies data) (copies_suffice data) pin
end Placement

/-- Construct the original pair-label cell of each physical incidence
from actual endpoint indices and primitive symbol readings. -/
def originalData [DecidableEq I] (special : I) (tie : F → Option B)
    (var : E → V) (fac : E → F) (cfg : Primitive V F B I → S) :
    IncidenceData I S E V F where
  var := var
  factor := fac
  wordVar := J1MainSourceLabels.variableWord cfg
  wordFactor := factorWord special tie cfg

theorem explicit_size_guard [Fintype I] [Fintype S] [Nonempty S] [Fintype A]
    (h : 48 * Fintype.card I * Fintype.card S ^ 2 *
        Fintype.card S ^ Fintype.card I < Fintype.card A) :
    (11/6 : ℚ) + 8*(Fintype.card (I×S) : ℚ)/
      ((Fintype.card A : ℚ)*DiagonalAbundance.successProb (I := I) (S := S)) < 2 := by
  let q : ℚ := Fintype.card I
  let r : ℚ := Fintype.card S
  let K : ℚ := r^Fintype.card I
  let n : ℚ := Fintype.card A
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hprod : 0 < r*K := mul_pos hr (pow_pos hr _)
  have hh : 48*q*r^2*K < n := by
    dsimp [q,r,K,n]
    exact_mod_cast h
  have hx : 48*(q*r) < n/(r*K) := by
    apply (lt_div_iff₀ hprod).2
    calc
      48*(q*r)*(r*K) = 48*q*r^2*K := by ring
      _ < n := hh
  have hmu : 0 < n/(r*K) := by
    have hnon : 0 ≤ 48*(q*r) := by
      have hq : 0 ≤ q := by dsimp [q]; positivity
      positivity
    exact lt_of_le_of_lt hnon hx
  have hsmall : 8*(q*r)/(n/(r*K)) < 1/6 := by
    apply (div_lt_iff₀ hmu).2
    linarith
  rw [Fintype.card_prod,Nat.cast_mul]
  change (11/6 : ℚ)+8*(q*r)/(n*((r*K)⁻¹)) < 2
  rw [← div_eq_mul_inv]
  linarith

section Existence
variable [Fintype I] [DecidableEq I] [Nonempty I] [Fintype S] [DecidableEq S] [Nonempty S]
variable [Fintype V] [Fintype F] [Fintype B] [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A]
variable [DecidableEq V] [DecidableEq F] [DecidableEq B]

/-- Actual primitive law, actual occupied incidence array, actual tracked
subtype. The prerequisites left here are the two graph-dependent mean cost
estimates, the independent-set premise and basic finite size bound. -/
theorem exists_actual_main_layout (special : I) (tie : F → Option B)
    (var : E → V) (fac : E → F) (pin : A → E)
    (pvar : A ↪ V) (pfac : A ↪ F) (pvertex : A ↪ V) (block : V → B)
    (hv : ∀ a, var (pin a) = pvar a) (hf : ∀ a, fac (pin a) = pfac a)
    (ht : ∀ a, tie (pfac a) = some (block (pvertex a)))
    (hind : ∀ a a', ¬triangleEdge block (pvertex a) (pvertex a'))
    (N : ℕ) (hN : 0 < N)
    (phi xi : (Primitive V F B I → S) → ℚ)
    (hPhi0 : ∀ x, 0 ≤ phi x) (hXi0 : ∀ x, 0 ≤ xi x)
    (hPhi : DiagonalAbundance.mean phi ≤ 4*(12*(N:ℚ))+2*(N:ℚ))
    (hXi : DiagonalAbundance.mean xi ≤ (Fintype.card I : ℚ)*(4*(N:ℚ)))
    (hSize : 48 * Fintype.card I * Fintype.card S ^ 2 *
        Fintype.card S ^ Fintype.card I < Fintype.card A) :
    ∃ cfg : Primitive V F B I → S,
      phi cfg / (5*(12*(N:ℚ))) +
        xi cfg / ((Fintype.card I : ℚ)*(4*(N:ℚ))) < 2 ∧
      ∀ t g, ((Fintype.card A : ℚ)*DiagonalAbundance.successProb (I := I) (S := S))/2 <
        ((ownedPins (compiledLayout (originalData special tie var fac cfg) pin)
          t g Finset.univ).card : ℚ) := by
  classical
  let key : A × Bool × I ↪ Primitive V F B I :=
    ⟨drawKey special tie pvar pfac,
      tied_drawKey_injective special tie pvar pfac pvertex block ht hind⟩
  let Z := {p // p ∉ Set.range key} → S
  letI : Fintype Z := Fintype.ofFinite Z
  letI : Nonempty Z := ⟨fun _ => Classical.choice inferInstance⟩
  let swap := chart (S := S) key
  let allPhi : DiagonalAbundance.State A I S Z → ℚ := fun z => phi (swap.symm z)
  let allXi : DiagonalAbundance.State A I S Z → ℚ := fun z => xi (swap.symm z)
  have pφ : DiagonalAbundance.mean allPhi ≤ 4*(12*(N:ℚ))+2*(N:ℚ) := by
    change DiagonalAbundance.mean (fun z => phi (swap.symm z)) ≤ _
    rw [DiagonalAbundance.mean_equiv swap.symm]
    exact hPhi
  have pξ : DiagonalAbundance.mean allXi ≤ (Fintype.card I : ℚ)*(4*(N:ℚ)) := by
    change DiagonalAbundance.mean (fun z => xi (swap.symm z)) ≤ _
    rw [DiagonalAbundance.mean_equiv swap.symm]
    exact hXi
  obtain ⟨z,hscore,hcounts⟩ := DiagonalAbundance.source_joint_abundance N hN
    allPhi allXi (fun z => hPhi0 (swap.symm z)) (fun z => hXi0 (swap.symm z))
      pφ pξ (explicit_size_guard hSize)
  let cfg := swap.symm z
  have hc : z.1 = (originalData special tie var fac cfg).cell ∘ pin := by
    have hw : (swap cfg).1 = fun a =>
        (J1MainSourceLabels.variableWord cfg (pvar a),factorWord special tie cfg (pfac a)) :=
      chart_tied_words special tie pvar pfac pvertex block ht hind cfg
    rw [show swap cfg = z from swap.apply_symm_apply z] at hw
    rw [hw]
    funext a
    simp [originalData,IncidenceData.cell,hv a,hf a]
  refine ⟨cfg,hscore,?_⟩
  intro t g
  have hcount := hcounts t g
  rw [hc,hitCount_is_actual_card] at hcount
  change _ < ((ownedPins (enumerateLayout _ _ _ _) t g Finset.univ).card : ℚ)
  rwa [owned_card_hits]
end Existence

#print axioms copies_suffice
#print axioms explicit_size_guard
#print axioms exists_actual_main_layout


section Native
variable [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S] [Fintype E] [Fintype A]

noncomputable abbrev kOf (data : IncidenceData I S E V F) (pin : A → E) : ℕ :=
  Fintype.card (Diagonal data pin)

abbrev Menu (D : Type*) (data : IncidenceData I S E V F) (pin : A → E) :=
  NativeJ2.Address I S V (kOf data pin) ⊕
    (NativeJ2.Address I S V (kOf data pin) × S) ⊕ D

abbrev pubInterval (width : ℕ) :=
  printedInterval (Fintype.card S) (Fintype.card I) width

noncomputable def pubPolynomial (width : ℕ) : ℚ[X] :=
  intervalPolynomial ((printedStart (Fintype.card S) (Fintype.card I) width).toNat) width

noncomputable def sourceOracle {R O D : Type*} [CommSemiring R] [CommSemiring O]
    (data : IncidenceData I S E V F) (pin : A → E) (width : ℕ) (node : I → ℚ)
    (ψ : R →+* O) (p : (Fin (kOf data pin) → Bool) → Bool → D → R[X])
    (z : D → O) (targets ord : D → ℕ)
    (s : Fin (kOf data pin) → Bool) (b : Bool) : Menu D data pin → ℚ[X] × O := fun q =>
  match q with
  | .inl a =>
    (sourceCompletedProbe (compiledLayout data pin) (pubInterval (I := I) (S := S) width)
      (pubPolynomial (I := I) (S := S) width) node a.node Finset.univ
      a.fibre a.direction a.fixed s (a.other s b),0)
  | .inr (.inl (a,g)) =>
    (sourceGroupProbe (compiledLayout data pin) (pubInterval (I := I) (S := S) width)
      (pubPolynomial (I := I) (S := S) width) node a.node g Finset.univ
      (a.fibre g) a.direction a.fixed s (a.other s b g),0)
  | .inr (.inr d) =>
    (0,(2:O)^ord d * z d^targets d * (p s b d).eval₂ ψ (2*z d))

noncomputable def menuPrice (D : Type*) (data : IncidenceData I S E V F) (pin : A → E) (floor : ℕ) :
    Menu D data pin → ℕ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun _ => 2^(kOf data pin-floor)) (fun _ => 0))

/-- The actual copied MAIN array and actual interval now supply the layout
premises of NativeJ2. The graph-dependent lower bound concerns the literal
hit set, not any orphan abstract group. D still supplies its own primitive
valuation hypotheses. -/
theorem native_path_from_original_main {R O D : Type*} [CommSemiring R] [CommSemiring O]
    (data : IncidenceData I S E V F) (pin : A → E)
    (width floor : ℕ) (node : I → ℚ)
    (hr : 2 ≤ Fintype.card S) (hR : 32 ≤ width) (hq : 6*width ≤ Fintype.card I)
    (hHits : ∀ t g, floor ≤ (hits data pin t g).card)
    (ψ : R →+* O) (precision : ℕ) (hprecision : (2:O)^precision = 0)
    (p : (Fin (kOf data pin) → Bool) → Bool → D → R[X])
    (z : D → O) (targets ord : D → ℕ)
    (hord : ∀ d, targets d ≤ ord d)
    (hcoeff : ∀ s b d j, (2 : R) ^ (precision-targets d-j) ∣ (p s b d).coeff j)
    (tree : FiniteWeightedQueryTree.DecisionTree (Menu D data pin) (ℚ[X]×O))
    (correct : ∀ s b, FiniteWeightedQueryTree.evaluate
      (sourceOracle data pin width node ψ p z targets ord s b) tree = b) :
    ∃ s b, 2 ^ kOf data pin ≤ FiniteWeightedQueryTree.paid (menuPrice D data pin floor)
      (sourceOracle data pin width node ψ p z targets ord s b) tree := by
  have hz : 0 ∉ pubInterval (I := I) (S := S) width :=
    zero_not_mem_printedInterval hr hR hq
  have hn : ∀ t g, floor ≤ (ownedPins (compiledLayout data pin) t g Finset.univ).card := by
    intro t g
    exact (hHits t g).trans_eq (owned_card_hits data (copies data) (copies_suffice data) pin t g).symm
  obtain ⟨s,b,h⟩ := NativeJ2.mixed_of_native_registers (compiledLayout data pin)
    (pubInterval (I := I) (S := S) width) hz (pubPolynomial (I := I) (S := S) width)
    node hn ψ precision hprecision p z targets ord hord hcoeff tree
    (by
      intro s b
      calc
        _ = FiniteWeightedQueryTree.evaluate
            (sourceOracle data pin width node ψ p z targets ord s b) tree := by
          congr 1
          funext q
          rcases q with a | ⟨⟨a,g⟩|d⟩ <;> rfl
        _ = b := correct s b)
  refine ⟨s,b,h.trans_eq ?_⟩
  congr 1
  funext q
  rcases q with a | ⟨⟨a,g⟩|d⟩ <;> rfl

#print axioms native_path_from_original_main

end Native

end J1MainSourceBridge
