// SVA checker for and_gate
module and_gate_sva (
  input logic A,
  input logic B,
  input logic C,
  input logic Y
);

  // Sample on any input edge; use ##0 to allow combinational settle
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C
  ); endclocking

  // Functional equivalence (4-state accurate)
  ap_func: assert property (##0 (Y === (A & B & C)))
    else $error("and_gate mismatch: A=%b B=%b C=%b Y=%b", A, B, C, Y);

  // Known-output when inputs are known
  ap_known: assert property ((!$isunknown({A,B,C})) |-> ##0 (!$isunknown(Y)))
    else $error("and_gate X/Z on Y with known inputs: A=%b B=%b C=%b Y=%b", A, B, C, Y);

  // Y changes only because some input changed
  ap_no_spurious: assert property (@(posedge Y or negedge Y) ($changed(A) or $changed(B) or $changed(C)))
    else $error("and_gate spurious Y change without input activity");

  // Truth-table coverage (all 8 input combinations with expected Y)
  cp_000: cover property (##0 (A===0 && B===0 && C===0 && Y===0));
  cp_001: cover property (##0 (A===0 && B===0 && C===1 && Y===0));
  cp_010: cover property (##0 (A===0 && B===1 && C===0 && Y===0));
  cp_011: cover property (##0 (A===0 && B===1 && C===1 && Y===0));
  cp_100: cover property (##0 (A===1 && B===0 && C===0 && Y===0));
  cp_101: cover property (##0 (A===1 && B===0 && C===1 && Y===0));
  cp_110: cover property (##0 (A===1 && B===1 && C===0 && Y===0));
  cp_111: cover property (##0 (A===1 && B===1 && C===1 && Y===1));

  // Output toggle coverage
  cy_pos: cover property (@(posedge Y) 1);
  cy_neg: cover property (@(negedge Y) 1);

endmodule

// Bind into the DUT
bind and_gate and_gate_sva u_and_gate_sva (.A(A), .B(B), .C(C), .Y(Y));