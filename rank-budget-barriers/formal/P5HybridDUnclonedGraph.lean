import P5HybridClosurePorts
import J6R10RepackPrecision

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11000000

/-! The literal uncloned fixed-density Appendix D input. The four
occurrences of a variable feed two trivalent equalities joined by one
internal edge. Every occurrence and every internal edge is then
subdivided once. There is no variable cloning or cycle of clauses. -/
namespace Paper5.HybridDUncloned
open scoped Classical BigOperators Polynomial
open J6R10Repack Paper5.HybridClosure

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3)

abbrev Occ := W⊕(F×Bool)
abbrev Factor := W⊕F
abbrev Tree (W : Type) := W×Bool
abbrev Link := Occ F⊕W
abbrev Wire := Link F×Bool
abbrev Old := Tree W⊕Factor F

/-- The two occurrences in each half of the four-port tree. -/
def quadBits (k : Fin 4) : Bool×Bool :=
  (decide (2≤k.val),decide (k.val%2=1))

def quadIndex : Bool×Bool→Fin 4
  | (false,false) => 0
  | (false,true) => 1
  | (true,false) => 2
  | (true,true) => 3

def quad : Fin 4≃Bool×Bool :=
  ⟨quadBits,quadIndex,by decide,by decide⟩

/-- Only an incidence-index chart: no CNF variable is duplicated. -/
def occSite : Occ F≃Tree W×Bool :=
  (nonCycleOwner F cubic).trans
    ((Equiv.prodCongr (Equiv.refl W) quad).trans (Equiv.prodAssoc W Bool Bool).symm)

def variableOf (p : Occ F) : W := (occSite F cubic p).1.1

def factorOf : Occ F→Factor F
  | .inl v => .inl v
  | .inr (e,_) => .inr e

omit [Fintype W] in
theorem literal_pin_site (v : W) : occSite F cubic (.inl v) = ((v,false),false) := rfl

omit [Fintype W] in
theorem literal_left_endpoint (e : F) : variableOf F cubic (.inr (e,false))=e.val.1 := rfl

omit [Fintype W] in
theorem literal_right_endpoint (e : F) : variableOf F cubic (.inr (e,true))=e.val.2 := rfl

/-- Row and column endpoints after exactly one subdivision. The right
branch of `Link` is the internal equality-tree edge, not a clause. -/
def network : Network (Wire F) (Old F) (Link F) where
  row
    | (.inl p,false) => .inl (occSite F cubic p).1
    | (.inl p,true) => .inr (factorOf F p)
    | (.inr v,b) => .inl (v,b)
  col e := e.1

def pinWire (v : W) : Wire F := (.inl (.inl v),true)

omit [Fintype W] [DecidableEq W] in
theorem real_pin_injective : Function.Injective (pinWire F) :=
  fun _ _ h=>Sum.inl.inj (Sum.inl.inj (congrArg Prod.fst h))

omit [Fintype W] in
theorem pin_row_exact (v : W) (x : Wire F) :
    (network F cubic).row x=.inr (.inl v) ↔ x=pinWire F v := by
  rcases x with ⟨(p|u),b⟩
  · rcases p with p|e <;> cases b <;> simp [network,pinWire,factorOf]
  · cases b <;> simp [network,pinWire]

include cubic in
theorem literal_occurrence_count : Fintype.card (Occ F)=4*Fintype.card W := by
  have h := Fintype.card_congr (occSite F cubic)
  simp only [Fintype.card_prod,Fintype.card_bool] at h
  omega

include cubic in
theorem literal_link_count : Fintype.card (Link F)=5*Fintype.card W := by
  rw [Fintype.card_sum,literal_occurrence_count F cubic]
  omega

include cubic in
theorem physical_wire_count : Fintype.card (Wire F)=10*Fintype.card W := by
  rw [Fintype.card_prod,literal_link_count F cubic,Fintype.card_bool]
  omega

def sourceSize : ℕ := Fintype.card W+Fintype.card (Factor F)

omit [DecidableEq W] in
theorem literal_size_is_cnf (σ : W→Bool) :
    sourceSize F=Fintype.card W+(PinnedCNF.formula F σ).length := by
  simp [sourceSize,PinnedCNF.formula,Fintype.card_sum,Fintype.card_coe]

include cubic in
theorem literal_size_exact : 2*sourceSize F=7*Fintype.card W := by
  have h := GraphCutMoments.regular_edge_count F 3 cubic
  simp only [sourceSize,Fintype.card_sum,Fintype.card_coe]
  omega

include cubic in
theorem literal_size_bounds :
    Fintype.card W≤sourceSize F ∧ sourceSize F≤4*Fintype.card W ∧
    Fintype.card (Wire F)≤3*sourceSize F := by
  have h := literal_size_exact F cubic
  rw [physical_wire_count F cubic]
  omega

#print axioms quad
#print axioms literal_pin_site
#print axioms literal_left_endpoint
#print axioms literal_right_endpoint
#print axioms pin_row_exact
#print axioms literal_occurrence_count
#print axioms literal_link_count
#print axioms physical_wire_count
#print axioms literal_size_is_cnf
#print axioms literal_size_exact
#print axioms literal_size_bounds
end
end Paper5.HybridDUncloned
