import UgpLean.Universality.UWCARegisterUniversality

/-!
# UgpLean.Universality.TuringUniversal — UGP Turing Universality

The UGP substrate is Turing-universal via the UWCA register-machine route:

1. Minsky counter machines compute every total computable function
   (`RegisterMachine.minsky_counter_machine_turing_complete_1967`, one named axiom).
2. The UWCA CRT register file executes counter-machine programs step-for-step
   (`UWCARegisterUniversality.uwca_substrate_turing_universal`, zero sorry).

Rule 110 is a separate, correctly scoped result: one finite binary tile program
the UWCA can execute (`UWCA_simulates_rule110_binary` / `uwca_sweep_implements_rule110`).

Reference: P48 §sec:uwca, §sec:gte_as_program; Minsky (1967).
-/

namespace UgpLean.Universality

/-- The UGP substrate is Turing-universal (register-machine route). -/
theorem ugp_is_turing_universal : UGP_substrate_turing_universal :=
  ugp_turing_universal

end UgpLean.Universality
