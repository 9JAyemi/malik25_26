// SVA for logic_circuit
module logic_circuit_sva (
  input logic A1, A2, B1, B2, C1,
  input logic X
);

  // Sample on any edge of inputs/output to catch combinational changes
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2 or
    posedge C1 or negedge C1 or
    posedge X  or negedge X
  ); endclocking

  // Local terms
  let a_term = (A1 & A2);
  let b_term = (B1 & B2);
  let f     = (C1 | a_term | b_term);

  // Functional equivalence (when inputs are known, output must match)
  ap_func: assert property ( !$isunknown({A1,A2,B1,B2,C1}) |-> (X === f) );

  // Scenario coverage across OR-term space (and correctness of X)
  cp_000: cover property ( ({C1,a_term,b_term} == 3'b000) && (X==1'b0) );
  cp_001: cover property ( ({C1,a_term,b_term} == 3'b001) && (X==1'b1) );
  cp_010: cover property ( ({C1,a_term,b_term} == 3'b010) && (X==1'b1) );
  cp_011: cover property ( ({C1,a_term,b_term} == 3'b011) && (X==1'b1) );
  cp_100: cover property ( ({C1,a_term,b_term} == 3'b100) && (X==1'b1) );
  cp_101: cover property ( ({C1,a_term,b_term} == 3'b101) && (X==1'b1) );
  cp_110: cover property ( ({C1,a_term,b_term} == 3'b110) && (X==1'b1) );
  cp_111: cover property ( ({C1,a_term,b_term} == 3'b111) && (X==1'b1) );

  // Toggle coverage on all primary inputs and output
  cA1_r: cover property (@(posedge A1) 1);
  cA1_f: cover property (@(negedge A1) 1);
  cA2_r: cover property (@(posedge A2) 1);
  cA2_f: cover property (@(negedge A2) 1);
  cB1_r: cover property (@(posedge B1) 1);
  cB1_f: cover property (@(negedge B1) 1);
  cB2_r: cover property (@(posedge B2) 1);
  cB2_f: cover property (@(negedge B2) 1);
  cC1_r: cover property (@(posedge C1) 1);
  cC1_f: cover property (@(negedge C1) 1);
  cX_r:  cover property (@(posedge X)  1);
  cX_f:  cover property (@(negedge X)  1);

endmodule

// Bind into DUT
bind logic_circuit logic_circuit_sva u_logic_circuit_sva (.*);