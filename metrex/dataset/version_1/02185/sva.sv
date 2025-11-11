// SVA for nand_gate
// Bind this checker to the DUT to verify functionality, X-prop, and provide coverage.

checker nand_gate_sva (input logic A, B, SLEEP_B, X);
  // Fire on any relevant change
  default clocking @(posedge A or negedge A
                    or posedge B or negedge B
                    or posedge SLEEP_B or negedge SLEEP_B
                    or posedge X or negedge X); endclocking

  // Functional equivalence (when inputs are known)
  a_func: assert property (!$isunknown({A,B,SLEEP_B}) |=> X === ((~(A & B)) & SLEEP_B))
    else $error("nand_gate mismatch: X != ~(A&B) & SLEEP_B");

  // Sleep gating behavior
  a_sleep0_forces0: assert property ((SLEEP_B===1'b0 && !$isunknown({A,B})) |=> X===1'b0)
    else $error("nand_gate sleep: X not 0 when SLEEP_B=0");

  a_awake_behavior: assert property ((SLEEP_B===1'b1 && !$isunknown({A,B})) |=> X===~(A&B))
    else $error("nand_gate awake: X != ~(A&B) when SLEEP_B=1");

  // X-propagation sanity
  a_known_in_known_out: assert property (!$isunknown({A,B,SLEEP_B}) |=> !$isunknown(X))
    else $error("nand_gate X/Z on output with known inputs");

  a_x_only_from_input_x: assert property ($isunknown(X) |=> $isunknown({A,B,SLEEP_B}))
    else $error("nand_gate X/Z on output without any input X/Z");

  // Functional coverage
  c_awake_tt00: cover property (SLEEP_B===1'b1 && A===1'b0 && B===1'b0 && X===1'b1);
  c_awake_tt01: cover property (SLEEP_B===1'b1 && A===1'b0 && B===1'b1 && X===1'b1);
  c_awake_tt10: cover property (SLEEP_B===1'b1 && A===1'b1 && B===1'b0 && X===1'b1);
  c_awake_tt11: cover property (SLEEP_B===1'b1 && A===1'b1 && B===1'b1 && X===1'b0);
  c_sleep_any:  cover property (SLEEP_B===1'b0 && X===1'b0);
  c_sleep_to_wake: cover property (SLEEP_B===1'b0 ##1 SLEEP_B===1'b1);
  c_wake_to_sleep: cover property (SLEEP_B===1'b1 ##1 SLEEP_B===1'b0);
endchecker

bind nand_gate nand_gate_sva u_nand_gate_sva (.A(A), .B(B), .SLEEP_B(SLEEP_B), .X(X));