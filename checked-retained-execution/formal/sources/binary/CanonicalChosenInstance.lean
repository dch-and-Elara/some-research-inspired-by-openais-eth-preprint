import J6R110CanonicalMountCore
import J6R110CanonicalBitsAgreement

/-! Validated against the lawful binary-order instantiation only.
This is not a theorem that two distinct historical orders agree. -/
namespace Paper6CanonicalChosenInstance
set_option autoImplicit false
set_option warningAsError true
theorem actual_chosen_order_is_the_metered_prefix (e d : ℕ) (fit : d+1≤2^e) :
    J6R110CanonicalMount.SameOrder e d fit :=
  fun i => J6R110CanonicalBitsAgreement.zeroPrefix_eq_testBit e d i
#print axioms actual_chosen_order_is_the_metered_prefix
theorem the_paid_table_matches_every_actual_chosen_prefix (e d : ℕ)
    (he : 0<e) (fit : d+1≤2^e) :
    (J6R109CanonicalProbeTable.canonicalTable e (d+1)).result =
      J6R110CanonicalMount.OldOrderedBytes e d fit :=
  J6R110CanonicalMount.actual_canonical_bytes_of_same_order e d he fit
    (actual_chosen_order_is_the_metered_prefix e d fit)
#print axioms the_paid_table_matches_every_actual_chosen_prefix
end Paper6CanonicalChosenInstance
