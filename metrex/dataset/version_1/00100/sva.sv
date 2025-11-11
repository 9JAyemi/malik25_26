// SVA for johnson_counter: checks implemented rotate-left behavior, period, and basic coverage.
// Optional intent check for a true Johnson (twisted ring) can be enabled via CHECK_JOHNSON_INTENT.

`ifndef JOHNSON_COUNTER_SVA
`define JOHNSON_COUNTER_SVA

module johnson_counter_sva #(
  parameter int m = 4,
  parameter bit CHECK_JOHNSON_INTENT = 0
)(
  input  logic          clk,
  input  logic [m-1:0]  out
);

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity
  initial assert (m >= 2) else $fatal(1,"johnson_counter requires m>=2, got %0d", m);

  // Track past validity and depth for $past(...,m)
  logic past_valid; int unsigned cyc;
  initial begin past_valid = 1'b0; cyc = 0; end
  always_ff @(posedge clk) begin
    past_valid <= 1'b1;
    if (cyc < m) cyc <= cyc + 1;
  end

  // Implemented behavior: pure rotate-left by 1 bit each cycle
  assert property (cb
    disable iff (!past_valid || $isunknown(out) || $isunknown($past(out)))
    out == { $past(out)[m-2:0], $past(out)[m-1] }
  );

  // Invariant: popcount preserved under rotation
  assert property (cb
    disable iff (!past_valid || $isunknown(out) || $isunknown($past(out)))
    $countones(out) == $past($countones(out))
  );

  // Rotation periodicity: after exactly m steps, state repeats
  assert property (cb
    disable iff (cyc < m || $isunknown(out) || $isunknown($past(out, m)))
    out == $past(out, m)
  );

  // Optional design-intent check for a true Johnson counter (twisted ring)
  // NOTE: Will fail on current implementation unless that intent is met.
  generate if (CHECK_JOHNSON_INTENT) begin : g_johnson_intent
    assert property (cb
      disable iff (!past_valid || $isunknown(out) || $isunknown($past(out)))
      out == { $past(out)[m-2:0], ~ $past(out)[m-1] }
    );
  end endgenerate

  // Coverage
  cover property (cb past_valid && !$isunknown(out) && out != $past(out));              // activity
  cover property (cb cyc >= m && !$isunknown(out) && out == $past(out, m));             // full rotation observed
  cover property (cb past_valid && $onehot(out));                                       // ever one-hot
  cover property (cb past_valid && out == '0);                                          // ever all-zeros
  cover property (cb past_valid && out == '1);                                          // ever all-ones

endmodule

bind johnson_counter johnson_counter_sva #(.m(m)) u_johnson_counter_sva (.clk(clk), .out(out));

`endif