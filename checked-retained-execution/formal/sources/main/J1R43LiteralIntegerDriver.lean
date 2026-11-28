import J1R43LiteralIntegerScore
import J1R43LiteralPhysical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5900000
set_option maxRecDepth 1900
set_option maxSynthPendingDepth 18
set_option linter.unusedSectionVars false

/-! The constructive chooser can use only integer comparisons with the
fixed denominator. For every source order, the integer driver returns
the identical assignment, not just some second acceptable layout. -/
namespace J1R43Literal
open GuardExpectation J1PhysicalHost J1PhysicalIncidence J1PhysicalCertificate MainClonedCNF
noncomputable section

section General
variable {P A : Type*}

def chooseInt (f : A → ℤ) : List A → A → A
  | [], best => best
  | a::as, best => chooseInt f as (if f a<f best then a else best)

theorem chooseInt_same (fi : A→ℤ) (fr : A→ℚ)
    (hc : ∀ a b, fi a<fi b ↔ fr a<fr b) (as : List A) (best : A) :
    chooseInt fi as best=choose fr as best := by
  induction as generalizing best with
  | nil => rfl
  | cons a as ih =>
    unfold chooseInt choose better
    by_cases hi : fi a<fi best
    · have hr := (hc a best).mp hi
      simp only [if_pos hi,if_pos hr]
      exact ih _
    · have hr : ¬fr a<fr best := fun hr => hi ((hc a best).mpr hr)
      simp only [if_neg hi,if_neg hr]
      exact ih _

variable [DecidableEq P] [DecidableEq A] [Fintype A] [Nonempty A]

def chooseLayoutInt (score : (P → Option A) → ℤ) (alphabet : List A) (default : A) :
    List P → (P → Option A) → (P → A) × ℕ
  | [], _ => ⟨fun _ => default,0⟩
  | k::ks, state =>
    let a := chooseInt (fun a => score (Function.update state k (some a))) alphabet default
    let tail := chooseLayoutInt score alphabet default ks (Function.update state k (some a))
    ⟨Function.update tail.1 k a,tail.2+2*alphabet.length⟩

theorem integer_driver_same (fi : (P → Option A) → ℤ) (fr : Marginals P A → ℚ)
    (cmp : ∀ a b, fi a<fi b ↔ fr (partialWeight a)<fr (partialWeight b))
    (alphabet : List A) (default : A) (keys : List P) (state : P → Option A) :
    chooseLayoutInt fi alphabet default keys state =
      chooseLayout fr alphabet default keys (partialWeight state) := by
  induction keys generalizing state with
  | nil => rfl
  | cons k ks ih =>
    have hc :
        chooseInt (fun a => fi (Function.update state k (some a))) alphabet default =
          choose (fun a => fr (fixAt (partialWeight state) k a)) alphabet default := by
      apply chooseInt_same
      intro a b
      have h := cmp (Function.update state k (some a)) (Function.update state k (some b))
      rw [← partialWeight_fix state k a,← partialWeight_fix state k b] at h
      exact h
    simp only [chooseLayoutInt,chooseLayout,hc,ih,← partialWeight_fix]

end General

section Physical
variable {B I S : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
  [Nonempty I] [Fintype S] [DecidableEq S] [Nonempty S]

def sourceIntegerScore (M : Match B) (t : I) (H : Finset (Vertex B))
    (state : ConfigKey M I → Option S) : ℤ :=
  integerScore t (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
    (portFactor (edges M)) (pinSubset M H) state

theorem integer_selector_is_original (M : Match B) (t : I) (H : Finset (Vertex B))
    (hh : 0<H.card) (keys : List (ConfigKey M I)) (palette : List S) (default : S) :
    chooseLayoutInt (sourceIntegerScore M t H) palette default keys (fun _=>none) =
      selected M t H keys palette default := by
  have hN : 0<Fintype.card (Vertex B) := hh.trans_le (Finset.card_le_univ H)
  have hM : 0<Fintype.card (Port (edges M)) := by
    rw [port_card (edges M) (degree_eq_three M)]
    positivity
  have hV : 0<Fintype.card (Variable (Vertex B)) := by
    rw [variables_card]
    positivity
  have hH : 0<Fintype.card H := by simpa only [Fintype.card_coe] using hh
  have hI : 0<Fintype.card I := Fintype.card_pos
  have cmp (a b : ConfigKey M I → Option S) :
      sourceIntegerScore M t H a<sourceIntegerScore M t H b ↔
        compactOriginal M t H (partialWeight a) < compactOriginal M t H (partialWeight b) :=
    exact_integer_comparison t (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
      (portFactor (edges M)) (pinSubset M H) a hM hV hI hH b
  rw [integer_driver_same _ _ cmp,partialWeight_none]
  rfl

end Physical

#print axioms chooseInt_same
#print axioms integer_driver_same
#print axioms integer_selector_is_original

end
end J1R43Literal