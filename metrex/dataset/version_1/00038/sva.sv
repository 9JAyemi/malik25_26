// SVA for sky130_fd_sc_ms__nor2b: Y = (~A) & B_N
// Bind this checker to the DUT.

module sky130_fd_sc_ms__nor2b_sva (input logic A, B_N, Y);

  // Sample on any input edge to model combinational behavior
  default clocking cb @(posedge A or negedge A or posedge B_N or negedge B_N); endclocking

  // Functional correctness in 4-state logic (X/Z aware)
  a_func:       assert property (1 |-> ##0 (Y === ((~A) & B_N)))
                 else $error("Y != (~A)&B_N");

  // Output must be known when inputs are known
  a_known:      assert property (!$isunknown({A,B_N}) |-> ##0 !$isunknown(Y))
                 else $error("Y unknown while inputs known");

  // Redundant but explicit: Y high only in the single minterm A=0,B_N=1
  a_only_high:  assert property (Y===1'b1 |-> ##0 (A===1'b0 && B_N===1'b1))
                 else $error("Y high outside (~A & B_N)");

  // Truth-table coverage (all input combos observed with expected Y)
  c_t00: cover property (A===1'b0 && B_N===1'b0 && Y===1'b0);
  c_t01: cover property (A===1'b0 && B_N===1'b1 && Y===1'b1);
  c_t10: cover property (A===1'b1 && B_N===1'b0 && Y===1'b0);
  c_t11: cover property (A===1'b1 && B_N===1'b1 && Y===1'b0);

  // Toggle coverage on output and key causes
  c_y_rise:      cover property ($rose(Y));
  c_y_fall:      cover property ($fell(Y));
  c_rise_cause1: cover property ($rose(B_N) && A===1'b0 && Y===1'b1);
  c_rise_cause2: cover property ($fell(A)   && B_N===1'b1 && Y===1'b1);
  c_fall_cause1: cover property ($fell(B_N) && Y===1'b0);
  c_fall_cause2: cover property ($rose(A)   && Y===1'b0);

endmodule

// Bind into the DUT
bind sky130_fd_sc_ms__nor2b sky130_fd_sc_ms__nor2b_sva sva_i (.A(A), .B_N(B_N), .Y(Y));