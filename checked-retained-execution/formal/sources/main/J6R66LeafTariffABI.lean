import J6R49LeafRowRecord

/-! The proof-selected fallback format alone does not describe an
efficient compiler. Even on a fixed positive-edge call one can replace
a free original gate by (n) copies of the same address to an equality
gate. It reads the same exact value and passes the same format. -/
namespace J6R66LeafTariff
open scoped Polynomial
open AOracleMachineTime J6R21Leaf J6R24MeteredRecursion J6ActiveRun J6R11Blueprint
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48Leaf J6R49Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false

private theorem scan_repeated_address {m k : ℕ} (a : BitAddress m k) (bits : List Bool) (n : ℕ) :
    (scanWords bits (List.replicate n a)).result=
      List.replicate n (readAddress a bits).result := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ,scanWords,List.replicate_succ]; exact congrArg (List.cons _) ih

private theorem identical_bits_equal (b : Bool) (n : ℕ) :
    localAllEqual (List.replicate n b)=true := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [List.replicate_succ,localAllEqual,List.headD_cons,List.all_eq_true,
      beq_iff_eq]
    intro x hx
    apply List.eq_of_mem_replicate
    rw [List.replicate_succ]
    exact hx

theorem repeated_equal_reads_free {m k : ℕ} (a : BitAddress m k) (bits : List Bool) (n : ℕ) :
    let r := runOriginalGate bits (.equal (List.replicate n a))
    r.result=(runOriginalGate (m:=m) (k:=k) bits .free).result ∧
      5*n+4≤r.steps := by
  constructor
  · simp only [runOriginalGate,scan_repeated_address,identical_bits_equal]
  · change 5*n+4≤(scanWords bits (List.replicate n a)).steps+5*(List.replicate n a).length+4
    rw [List.length_replicate]
    omega

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
variable {c : Call (PhysicalHost f ell)} {hf : f.Monic} {F : Frame f c.prec} {pos : 0<ell}
variable {ord : Fin c.edges≃c.host.Edge} {v : Vertex c}
variable {live : Bank f ell key prec tw bw page→Prop}

/-- No change in source call, vertex, frame, bank, result, or receiver
precision. This counterexample concerns the public RowAt interface,
not the physical gate compiler on the canonical source path. -/
theorem free_row_spec_does_not_bound_actual_tape
    (row : RowAt hf F pos ord v live) {k : ℕ}
    (free : row.code=.original k .free) (address : BitAddress c.edges k) (n : ℕ) :
    ∃ r : RowAt hf F pos ord v live,
      r.code=.original k (.equal (List.replicate n address)) ∧
      ∀ (B : Bank f ell key prec tw bw page) bits, n≤(r.code.run hf F pos B bits).steps := by
  let code : PageReadCode c.edges key page := .original k (.equal (List.replicate n address))
  have value : ∀ (B : Bank f ell key prec tw bw page) bits, (code.run hf F pos B bits).result=(row.code.run hf F pos B bits).result := by
    intro B bits
    rw [free]
    change (uvGate F.hp F.sizePos pos (.equal (List.replicate n address)) bits).result=
      (uvGate F.hp F.sizePos pos (.free : OriginalGateTape c.edges k) bits).result
    simp only [uvGate,(repeated_equal_reads_free address bits n).1]
  refine ⟨⟨code,fun B h xs=>?_,fun _ _=>True.intro⟩,rfl,?_⟩
  · rw [value]
    exact row.value B h xs
  · intro B bits
    change n≤(uvGate F.hp F.sizePos pos (.equal (List.replicate n address)) bits).steps
    have h := (repeated_equal_reads_free address bits n).2
    change n≤(runOriginalGate bits (.equal (List.replicate n address))).steps+
      A1R11.uvWidth F.words.length ell c.prec+4
    omega

#print axioms repeated_equal_reads_free
#print axioms free_row_spec_does_not_bound_actual_tape
end J6R66LeafTariff
