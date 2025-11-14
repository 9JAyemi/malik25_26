// SVA for ring_counter. Bind this to the DUT.
// Focus: rotation correctness, period-N invariance, and invariants preserved by rotation.

module ring_counter_sva #(parameter int n = 4) (
  input logic               clk,
  input logic [n-1:0]       out
);

  default clocking cb @(posedge clk); endclocking

  // 1) One-step rotate-left behavior
  assert property (1 |-> ##1 out == { $past(out[n-2:0]), $past(out[n-1]) });

  // 2) After n cycles, state must repeat (rotate n times returns to original)
  assert property (1 |-> ##n (out == $past(out, n)));

  // 3) Rotation preserves number of 1s
  assert property (1 |-> ##1 ($countones(out) == $past($countones(out))));

  // 4) If previous state was one-hot, next state remains one-hot (ring-counter mode)
  assert property ($onehot($past(out)) |-> $onehot(out));

  // Coverage
  cover property ($onehot(out));                                   // see one-hot state at least once
  cover property ($onehot(out) ##[1:n] (out == $past(out, n)));    // see a full rotation while one-hot

  genvar i;
  generate
    for (i = 0; i < n; i++) begin : C_EACH_BIT_ONEHOT
      cover property ($onehot(out) && out[i]); // each bit observed as the '1' in one-hot mode
    end
  endgenerate

endmodule

// Bind into the DUT
bind ring_counter ring_counter_sva #(.n(n)) u_ring_counter_sva (.clk(clk), .out(out));