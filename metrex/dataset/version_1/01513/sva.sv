// SVA for d_flip_flop_chain
// Bind into the DUT to see internals
module dff_chain_sva (
  input        clk,
  input  [7:0] d,
  input  [7:0] q,
  input  [7:0] q_reg,
  input  [7:0] d_wire
);
  default clocking cb @(negedge clk); endclocking

  // establish valid past after first negedge
  bit past_valid;
  initial past_valid = 1'b0;
  always @(negedge clk) past_valid <= 1'b1;

  // Core functional check: 1-cycle negedge-latency DFF
  property p_q_tracks_d_on_negedge;
    disable iff (!past_valid)
      q == $past(d);
  endproperty
  assert property (p_q_tracks_d_on_negedge)
    else $error("q != $past(d) at negedge");

  // No spurious X creation: X on sampled d propagates to q next cycle
  property p_x_propagation;
    disable iff (!past_valid)
      $isunknown($past(d)) |-> $isunknown(q);
  endproperty
  assert property (p_x_propagation)
    else $error("q not X when $past(d) is X");

  // Structural consistency checks
  // q is a direct mirror of q_reg
  assert property (@(posedge clk or negedge clk) q == q_reg)
    else $error("q != q_reg");

  // Truncation guard: as coded, d_wire must equal d (concatenation truncates)
  assert property (@(posedge clk or negedge clk) d_wire == d)
    else $error("d_wire != d (unexpected concatenation effect)");

  // Coverage
  cover property (@(negedge clk) past_valid && !$isunknown(d) && q == $past(d));
  cover property (@(negedge clk) past_valid && !$isunknown(d) && q != $past(q)); // q changed
  cover property (@(negedge clk) past_valid && q == 8'h00);
  cover property (@(negedge clk) past_valid && q == 8'hFF);
endmodule

bind d_flip_flop_chain dff_chain_sva u_dff_chain_sva (
  .clk(clk),
  .d(d),
  .q(q),
  .q_reg(q_reg),
  .d_wire(d_wire)
);