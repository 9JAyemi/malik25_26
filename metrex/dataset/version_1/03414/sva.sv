// SVA for sky130_fd_sc_ms__nor2
// Concise checks and full functional coverage

module sky130_fd_sc_ms__nor2_sva (input logic A, B, Y);

  // Sample on any edge of inputs/outputs
  // (works for pure combinational DUTs without a clock)
  property ev; @(posedge A or negedge A or posedge B or negedge B or posedge Y or negedge Y) 1; endproperty

  // Functional correctness when inputs are known
  assert property (ev |-> (!$isunknown({A,B})) |-> (Y === ~(A | B)))
    else $error("NOR2 func mismatch: A=%b B=%b Y=%b", A, B, Y);

  // Necessary conditions that must always hold
  assert property (ev |-> (Y === 1'b1) |-> (A === 1'b0 && B === 1'b0))
    else $error("NOR2 violation: Y==1 requires A==0 and B==0 (A=%b B=%b Y=%b)", A, B, Y);

  assert property (ev |-> ((A === 1'b1) || (B === 1'b1)) |-> (Y === 1'b0))
    else $error("NOR2 violation: any input==1 requires Y==0 (A=%b B=%b Y=%b)", A, B, Y);

  // Functional coverage: all truth table points
  cover property (ev and (A===1'b0 && B===1'b0 && Y===1'b1));
  cover property (ev and (A===1'b0 && B===1'b1 && Y===1'b0));
  cover property (ev and (A===1'b1 && B===1'b0 && Y===1'b0));
  cover property (ev and (A===1'b1 && B===1'b1 && Y===1'b0));

endmodule

// Bind SVA to the DUT
bind sky130_fd_sc_ms__nor2 sky130_fd_sc_ms__nor2_sva u_nor2_sva (.A(A), .B(B), .Y(Y));