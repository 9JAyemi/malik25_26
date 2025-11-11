// SVA for Test: checks functional correctness and adds concise coverage.
// Bind this file to the DUT: bind Test Test_sva u_test_sva(.clk(clk), .rc(rc), .rc_next(rc_next), .o(o));

module Test_sva (
  input logic        clk,
  input logic [63:0] rc,
  input logic [63:0] rc_next,
  input logic        o
);

  default clocking cb @(posedge clk); endclocking

  // Track valid past sample
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Correctness of registered computations (1-cycle latency)
  a_rc_next_correct: assert property (past_valid |-> rc_next == $past({rc[62:0], rc[63]^rc[2]^rc[0]}));
  a_o_correct:       assert property (past_valid |-> o       == $past((rc[0]^rc[1]) & (rc[62]^rc[63])));

  // X-propagation guards (only check when inputs are known)
  a_rc_next_no_x: assert property (past_valid && !$isunknown($past(rc)) |-> !$isunknown(rc_next));
  a_o_no_x:       assert property (past_valid && !$isunknown($past({rc[0],rc[1],rc[62],rc[63]})) |-> !$isunknown(o));

  // Functional coverage
  // Output covers
  c_o_0: cover property (past_valid && o == 1'b0);
  c_o_1: cover property (past_valid && o == 1'b1);

  // LFSR tap XOR (new bit) covers
  c_poly_0: cover property (past_valid && $past(rc[63]^rc[2]^rc[0]) == 1'b0);
  c_poly_1: cover property (past_valid && $past(rc[63]^rc[2]^rc[0]) == 1'b1);

  // Cross coverage of the two XOR terms that form o
  c_xor_00: cover property (past_valid && ($past(rc[0]^rc[1]) == 1'b0) && ($past(rc[62]^rc[63]) == 1'b0));
  c_xor_01: cover property (past_valid && ($past(rc[0]^rc[1]) == 1'b0) && ($past(rc[62]^rc[63]) == 1'b1));
  c_xor_10: cover property (past_valid && ($past(rc[0]^rc[1]) == 1'b1) && ($past(rc[62]^rc[63]) == 1'b0));
  c_xor_11: cover property (past_valid && ($past(rc[0]^rc[1]) == 1'b1) && ($past(rc[62]^rc[63]) == 1'b1));

endmodule

// Example bind (place outside the module or in a separate file):
// bind Test Test_sva u_test_sva(.clk(clk), .rc(rc), .rc_next(rc_next), .o(o));