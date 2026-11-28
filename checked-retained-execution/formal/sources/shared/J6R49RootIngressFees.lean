import J6R49RootIngressAssembly

/-! Paid syntax cleanup, guard and sign reads for the original root.
Preparing the position-only atlas is a separately supplied bill; it
cannot disappear into this metered compilation. -/
namespace J6R49RootIngress
open scoped Classical
open Std.Sat AOracleMachineTime J7R10Plant J6R30GeneratedRootLayout
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5600000

private theorem original_clean_is_shorter {V : Type*} [DecidableEq V] (F : CNF V) :
    (J7R9Clause.clean F).length≤F.length := by
  induction F with
  | nil => simp [J7R9Clause.clean]
  | cons c F ih => cases h : J7R9Clause.taut c <;> simp [J7R9Clause.clean,h] <;> omega

theorem guard_length_bound {V : Type*} [DecidableEq V] [Fintype V] (F : CNF V) :
    (guarded F).length≤F.length+Fintype.card V := by
  simp only [J7R9SourceInput.H,J6Guard.guardedFormula,List.length_append,List.length_map,
    Finset.length_toList,Finset.card_univ]
  exact Nat.add_le_add_right (original_clean_is_shorter F) _

theorem paid_full_ingress_fee {V : Type*} [DecidableEq V] [Fintype V]
    (F : CNF V) (code : V→List Bool) (inj : Function.Injective code)
    (w : ℕ) (width : ∀ v,(code v).length=w)
    (rank : ∀ c∈F,c.length≤3)
    {r c d h : ℕ} (pos : List (Position r c d h)) :
    (compileRootIngress ((Finset.univ : Finset V).toList.map code) (codeCNF code F) pos).steps≤
      fullIngressFee w 3 F.length (Fintype.card V)+
        (1+pos.length*signFee r c d h 4 (F.length+Fintype.card V))+5 := by
  let keys := (Finset.univ : Finset V).toList.map code
  let inBits := codeCNF code F
  let A := guardedMeter keys inBits
  have hkeys : ∀ q∈keys,q.length=w := by
    intro q hq
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hq
    exact width v
  have hRawWidth : ∀ a∈inBits,a.length≤3 := by
    intro a ha
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
    simpa only [List.length_map] using rank k hk
  have hWords : ∀ a∈inBits,∀ b∈a,b.1.length=w := by
    intro a ha b hb
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hb
    exact width q.1
  have C := paid_guard_source_cost keys inBits w 3 hkeys hRawWidth hWords
  change A.steps≤_ at C
  have C' : A.steps≤fullIngressFee w 3 F.length (Fintype.card V) := by
    simpa only [keys,inBits, codeCNF,List.length_map,Finset.length_toList,Finset.card_univ] using C
  have E : A.result=codeCNF (guardCode code) (guarded F) := paid_guard_original_syntax code inj F
  have W : ∀ a∈A.result,a.length≤4 := by
    rw [E]
    intro a ha
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
    simpa only [List.length_map] using J7R9SourceInput.width_four F rank k hk
  have len : A.result.length≤F.length+Fintype.card V := by
    rw [E]
    simpa only [codeCNF,List.length_map] using guard_length_bound F
  have fee : signFee r c d h 4 A.result.length≤signFee r c d h 4 (F.length+Fintype.card V) := by
    unfold signFee
    gcongr
  have B := (signed_atlas_steps A.result pos 4 W).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ fee) 1)
  change A.steps+(signAtlas A.result pos).steps+5≤_
  exact Nat.add_le_add_right (Nat.add_le_add C' B) 5

def billedRootIngress {r c d h : ℕ} (declares : List (List Bool)) (raw : BitsCNF)
    (atlas : Meter (List (Position r c d h))) :
    Meter (Option (List (SignedHalfPort r c d))) :=
  let compile := compileRootIngress declares raw atlas.result
  ⟨compile.result,atlas.steps+compile.steps+3⟩

theorem billed_compiler_counts_the_atlas {r c d h : ℕ} (declares : List (List Bool)) (raw : BitsCNF)
    (atlas : Meter (List (Position r c d h))) :
    (billedRootIngress declares raw atlas).result=(compileRootIngress declares raw atlas.result).result ∧
    (billedRootIngress declares raw atlas).steps=atlas.steps+(compileRootIngress declares raw atlas.result).steps+3 :=
  ⟨rfl,rfl⟩

#print axioms guard_length_bound
#print axioms paid_full_ingress_fee
#print axioms billed_compiler_counts_the_atlas
end J6R49RootIngress
