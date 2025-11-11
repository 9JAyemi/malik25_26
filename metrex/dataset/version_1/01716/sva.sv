// SVA for flipflop_adder
module flipflop_adder_sva (
  input        clk,
  input  [7:0] reset,
  input  [7:0] d,
  input  [7:0] q,
  input  [7:0] q_reg,
  input  [7:0] sum
);

  default clocking cb @(negedge clk); endclocking

  // Basic sanity (no X/Z at sample)
  a_no_x_inputs: assert property (!$isunknown({clk, reset, d}));
  a_no_x_state:  assert property (!$isunknown({q_reg, sum, q}));

  // Per-bit synchronous behavior
  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : G_PERBIT
      // If reset[i] is 1 at a negedge, next cycle that bit clears to 0
      a_reset_clears:      assert property (reset[i] |=> (q_reg[i] == 1'b0));
      // If reset[i] is 0 at a negedge, next cycle captures d[i]
      a_capture_on_no_rst: assert property (!reset[i] |=> (q_reg[i] == $past(d[i])));
      // Coverage: exercise both paths
      c_bit_reset:         cover property (reset[i]);
      c_bit_set:           cover property (!reset[i] && d[i] |=> q_reg[i]);
    end
  endgenerate

  // Combinational relations (after NBA updates in same timestep)
  a_sum_correct: assert property (1'b1 |-> ##0 (sum == $countones(q_reg)));
  a_q_eq_sum:    assert property (1'b1 |-> ##0 (q == sum));

  // Range check (sum of 8 one-bit flops is 0..8)
  a_q_range:     assert property (q <= 8);

  // Interesting coverage on totals
  c_q_zero:   cover property ($countones(q_reg) == 0 && q == 0);
  c_q_eight:  cover property ($countones(q_reg) == 8 && q == 8);
  c_midrange: cover property ($countones(q_reg) inside {[1:7]});
endmodule

// Bind into DUT (accesses internal q_reg and sum)
bind flipflop_adder flipflop_adder_sva i_flipflop_adder_sva (
  .clk(clk), .reset(reset), .d(d), .q(q), .q_reg(q_reg), .sum(sum)
)