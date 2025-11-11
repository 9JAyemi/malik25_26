// SVA for johnson_counter
// Checks reset behavior, next-state function, out==q, no Xs, and rotation periodicity.
// Includes concise coverage of key sequences.

module johnson_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [2:0]  out,
  input  logic [2:0]  q
);

  default clocking cb @(posedge clk); endclocking

  // Reset drives zero on the next cycle
  a_reset_clears: assert property (reset |=> (q == 3'b000 && out == 3'b000));

  // out must always mirror q when not in reset
  a_out_mirrors_q: assert property (!reset |-> (out == q));

  // No X/Z on observable/register signals when not in reset
  a_no_unknowns: assert property (!reset |-> !$isunknown({q,out}));

  // Functional next-state relation when reset is low across the boundary
  a_next_state: assert property ((!reset && !$past(reset,1,1'b1))
                                 |-> (q == { $past(q,1,3'b000)[1:0], $past(q,1,3'b000)[2] }));

  // Degenerate fixed points are consistent with next-state function
  a_zero_holds: assert property ((!reset && q == 3'b000) |-> ##1 (q == 3'b000));
  a_ones_holds: assert property ((!reset && q == 3'b111) |-> ##1 (q == 3'b111));

  // For any non-trivial seed, rotation returns in 3 cycles (while reset stays low)
  a_period3: assert property ((!reset && q != 3'b000 && q != 3'b111)
                              |-> (!reset)[*3] ##3 (q == $past(q,3)));

  // Coverage

  // Reset observed and clears to 0
  c_reset_seen:   cover property (reset);
  c_reset_clear:  cover property (reset |=> (q == 3'b000));

  // Observe the two 3-state rotation orbits (if a non-zero seed occurs)
  c_orbit_001: cover property (!reset && q==3'b001 ##1 !reset && q==3'b010 ##1 !reset && q==3'b100 ##1 !reset && q==3'b001);
  c_orbit_011: cover property (!reset && q==3'b011 ##1 !reset && q==3'b110 ##1 !reset && q==3'b101 ##1 !reset && q==3'b011);

  // Observe degenerate fixed points
  c_zero_lock: cover property (!reset && q==3'b000 ##1 !reset && q==3'b000);
  c_ones_lock: cover property (!reset && q==3'b111 ##1 !reset && q==3'b111);

endmodule

// Bind into DUT to access internal q
bind johnson_counter johnson_counter_sva u_johnson_counter_sva (
  .clk  (clk),
  .reset(reset),
  .out  (out),
  .q    (q)
);