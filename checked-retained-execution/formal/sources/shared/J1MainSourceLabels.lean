import DiagonalAbundance
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

/-! Actual primitive MAIN label keys in J1. Factor words can share
one designated coordinate within one triangle. All other coordinates
are indexed by the original factor/variable. A graph-independent pin set
gives a Cartesian-product block of independent double words. -/
namespace J1MainSourceLabels
open DiagonalAbundance
universe u v w i p s

abbrev Primitive (V : Type u) (F : Type v) (B : Type w) (I : Type i) :=
  (V × I) ⊕ ((F × I) ⊕ B)

variable {V : Type u} {F : Type v} {B : Type w} {I : Type i} {A : Type p}
    {S : Type s}

def factorKey [DecidableEq I] (special : I) (tie : F → Option B) (f : F) (t : I) :
    (F × I) ⊕ B :=
  if t = special then (tie f).elim (Sum.inl (f,t)) Sum.inr
  else Sum.inl (f,t)

def variableWord (cfg : Primitive V F B I → S) (v : V) : I → S :=
  fun t => cfg (Sum.inl (v,t))

def factorWord [DecidableEq I] (special : I) (tie : F → Option B)
    (cfg : Primitive V F B I → S) (f : F) : I → S :=
  fun t => cfg (Sum.inr (factorKey special tie f t))

theorem common_factor_coordinate [DecidableEq I] (special : I) (tie : F → Option B)
    (cfg : Primitive V F B I → S) {f f' : F} {b : B}
    (hf : tie f = some b) (hg : tie f' = some b) :
    factorWord special tie cfg f special = factorWord special tie cfg f' special := by
  simp [factorWord,factorKey,hf,hg]

/-- The actual triangle edges join different vertices with the same
triangle label. Reserve may remove vertices but cannot introduce another
member of a triangle into an independent candidate set. -/
def triangleEdge (block : V → B) (v w : V) : Prop :=
  v ≠ w ∧ block v = block w

theorem triangle_blocks_unique_on_independent (block : V → B) (pinVertex : A ↪ V)
    (hind : ∀ a a', ¬ triangleEdge block (pinVertex a) (pinVertex a')) :
    Function.Injective (fun a => block (pinVertex a)) := by
  intro a a' he
  apply pinVertex.injective
  by_contra hh
  exact hind a a' ⟨hh,he⟩

/-- Distinct tracked pin factors do not share a primitive entry if they
have different triangle tags. Ordinary untied factors need only be distinct. -/
theorem pin_factorKey_injective [DecidableEq I] (special : I) (tie : F → Option B)
    (pinFactor : A ↪ F)
    (hblock : ∀ a a' b, tie (pinFactor a) = some b →
      tie (pinFactor a') = some b → a = a') :
    Function.Injective (fun p : A × I => factorKey special tie (pinFactor p.1) p.2) := by
  rintro ⟨a,i⟩ ⟨a',j⟩ h
  change factorKey special tie (pinFactor a) i = factorKey special tie (pinFactor a') j at h
  by_cases hi : i = special <;> by_cases hj : j = special
  · subst i; subst j
    cases ha : tie (pinFactor a) <;> cases hb : tie (pinFactor a') <;>
      simp [factorKey,ha,hb] at h
    · exact Prod.ext h rfl
    · subst_vars
      exact Prod.ext (hblock a a' _ ha hb) rfl
  · subst i
    cases ha : tie (pinFactor a)
    · simp [factorKey,ha,hj] at h
      exact False.elim (hj h.2.symm)
    · simp [factorKey,ha,hj] at h
  · subst j
    cases hb : tie (pinFactor a')
    · simp [factorKey,hb,hi] at h
    · simp [factorKey,hb,hi] at h
  · simp [factorKey,hi,hj] at h
    exact Prod.ext h.1 h.2

/-- Selection of the original variable-word symbols and original factor-word
symbols for a graph-only candidate pin. -/
def drawKey [DecidableEq I] (special : I) (tie : F → Option B)
    (pinVar : A ↪ V) (pinFactor : A ↪ F) (p : A × Bool × I) :
    Primitive V F B I :=
  if p.2.1 then Sum.inr (factorKey special tie (pinFactor p.1) p.2.2)
  else Sum.inl (pinVar p.1,p.2.2)

theorem drawKey_injective [DecidableEq I] (special : I) (tie : F → Option B)
    (pinVar : A ↪ V) (pinFactor : A ↪ F)
    (hblock : ∀ a a' b, tie (pinFactor a) = some b →
      tie (pinFactor a') = some b → a = a') :
    Function.Injective (drawKey special tie pinVar pinFactor) := by
  rintro ⟨a,l,i⟩ ⟨b,r,j⟩ h
  cases l <;> cases r <;> simp [drawKey] at h
  · exact Prod.ext h.1 (Prod.ext rfl h.2)
  · have hh : (a,i) = (b,j) := pin_factorKey_injective special tie pinFactor hblock h
    cases hh
    rfl

theorem tied_drawKey_injective [DecidableEq I] (special : I) (tie : F → Option B)
    (pinVar : A ↪ V) (pinFactor : A ↪ F) (pinVertex : A ↪ V) (block : V → B)
    (ht : ∀ a, tie (pinFactor a) = some (block (pinVertex a)))
    (hind : ∀ a a', ¬ triangleEdge block (pinVertex a) (pinVertex a')) :
    Function.Injective (drawKey special tie pinVar pinFactor) := by
  apply drawKey_injective
  intro a a' b ha hb
  apply triangle_blocks_unique_on_independent block pinVertex hind
  exact Option.some.inj ((ht a).symm.trans (ha.trans (hb.symm.trans (ht a'))))

/-- Explicitly split the independent primitive symbols used by the candidate
pins from the unused symbols. The double-word block is uniform because this
is a bijection of full finite sample spaces. -/
noncomputable def chart {U : Type*} (key : A × Bool × I ↪ U) :
    (U → S) ≃ ((A → Draw I S) × ({u // u ∉ Set.range key} → S)) := by
  classical
  let split := Equiv.piEquivPiSubtypeProd (fun u => u ∈ Set.range key) (fun _ => S)
  let rangeEquiv := Equiv.ofInjective key key.injective
  let flatten : ({u // u ∈ Set.range key} → S) ≃ ((A × Bool × I) → S) :=
    Equiv.piCongrLeft' (fun _ => S) rangeEquiv.symm
  let curry : ((A × Bool × I) → S) ≃ (A → Draw I S) :=
    (Equiv.curry A (Bool × I) S).trans <|
      Equiv.piCongrRight (fun _ =>
        (Equiv.curry Bool I S).trans (Equiv.boolArrowEquivProd (I → S)))
  exact split.trans ((flatten.trans curry).prodCongr (Equiv.refl _))

theorem chart_first_of_key {U : Type*} (key : A × Bool × I ↪ U)
    (cfg : U → S) (a : A) (t : I) :
    ((chart key cfg).1 a).1 t = cfg (key (a,false,t)) ∧
    ((chart key cfg).1 a).2 t = cfg (key (a,true,t)) := by
  constructor <;> rfl

/-- Thus the sampled words of the actual tied layout are precisely those
in the independent block, not copies chosen in a different distribution. -/
theorem chart_tied_words [DecidableEq I] (special : I) (tie : F → Option B)
    (pinVar : A ↪ V) (pinFactor : A ↪ F) (pinVertex : A ↪ V) (block : V → B)
    (ht : ∀ a, tie (pinFactor a) = some (block (pinVertex a)))
    (hind : ∀ a a', ¬ triangleEdge block (pinVertex a) (pinVertex a'))
    (cfg : Primitive V F B I → S) :
    let key : A × Bool × I ↪ Primitive V F B I :=
      ⟨drawKey special tie pinVar pinFactor,
        tied_drawKey_injective special tie pinVar pinFactor pinVertex block ht hind⟩
    (chart key cfg).1 = fun a =>
      (variableWord cfg (pinVar a), factorWord special tie cfg (pinFactor a)) := by
  intro key
  funext a
  apply Prod.ext
  · funext t
    exact (chart_first_of_key key cfg a t).1
  · funext t
    exact (chart_first_of_key key cfg a t).2

#print axioms common_factor_coordinate
#print axioms triangle_blocks_unique_on_independent
#print axioms pin_factorKey_injective
#print axioms tied_drawKey_injective
#print axioms chart_first_of_key
#print axioms chart_tied_words

end J1MainSourceLabels
