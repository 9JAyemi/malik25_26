// SVA for nand_gate and and_gate
// Bind these to the DUTs; concise, edge-based sampling with ##0 to avoid delta races.

module nand_gate_sva (input logic A, B, X);
  // Functional correctness
  property p_nand_func;
    @(posedge A or negedge A or posedge B or negedge B)
      (!$isunknown({A,B})) |-> ##0 (X === ~(A & B));
  endproperty
  a_nand_func: assert property (p_nand_func);

  // Truth-table coverage
  c_nand_00: cover property (@(posedge A or negedge A or posedge B or negedge B)
                             (!$isunknown({A,B})) ##0 (A==0 && B==0 && X==1));
  c_nand_01: cover property (@(posedge A or negedge A or posedge B or negedge B)
                             (!$isunknown({A,B})) ##0 (A==0 && B==1 && X==1));
  c_nand_10: cover property (@(posedge A or negedge A or posedge B or negedge B)
                             (!$isunknown({A,B})) ##0 (A==1 && B==0 && X==1));
  c_nand_11: cover property (@(posedge A or negedge A or posedge B or negedge B)
                             (!$isunknown({A,B})) ##0 (A==1 && B==1 && X==0));
endmodule

module and_gate_sva (input logic A, B, X);
  // AND functionality (this will flag the design bug if X != A & B)
  property p_and_func;
    @(posedge A or negedge A or posedge B or negedge B)
      (!$isunknown({A,B})) |-> ##0 (X === (A & B));
  endproperty
  a_and_func: assert property (p_and_func);

  // Truth-table coverage
  c_and_00: cover property (@(posedge A or negedge A or posedge B or negedge B)
                            (!$isunknown({A,B})) ##0 (A==0 && B==0 && X==0));
  c_and_01: cover property (@(posedge A or negedge A or posedge B or negedge B)
                            (!$isunknown({A,B})) ##0 (A==0 && B==1 && X==0));
  c_and_10: cover property (@(posedge A or negedge A or posedge B or negedge B)
                            (!$isunknown({A,B})) ##0 (A==1 && B==0 && X==0));
  c_and_11: cover property (@(posedge A or negedge A or posedge B or negedge B)
                            (!$isunknown({A,B})) ##0 (A==1 && B==1 && X==1));

  // Edge-response coverage (useful to catch/confirm correct edge behavior)
  c_and_roseA_hits_X: cover property (@(posedge A) (B===1) ##0 $rose(X));
  c_and_roseB_hits_X: cover property (@(posedge B) (A===1) ##0 $rose(X));
  c_and_fallA_drops_X: cover property (@(negedge A) (B===1) ##0 $fell(X));
  c_and_fallB_drops_X: cover property (@(negedge B) (A===1) ##0 $fell(X));
endmodule

// Bind to DUTs
bind nand_gate nand_gate_sva u_nand_gate_sva(.A(A), .B(B), .X(X));
bind and_gate  and_gate_sva  u_and_gate_sva (.A(A), .B(B), .X(X));