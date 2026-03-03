// SVA for BusHold. Bind this to the DUT.
// Quality-focused, concise checks and useful coverage.

module BusHold_sva #(parameter int n = 8) (
  input  logic             clk,
  input  logic             rst,
  input  logic [n-1:0]     in,
  input  logic [n-1:0]     out
);

  // Static parameter check
  initial if (n <= 0) $error("BusHold: n must be > 0");

  default clocking cb @(posedge clk); endclocking

  // History tracker
  logic past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset behavior: synchronous reset forces out to 0 on the reset cycle
  a_rst_zero:       assert property (rst |-> out == '0);

  // Immediately after a reset cycle, out remains 0 (since hold was loaded with 0)
  a_postrst_zero:   assert property (past_valid && !rst && $past(rst) |-> out == '0);

  // Functional behavior: in normal operation, out equals previous in (1-cycle latency)
  a_capture:        assert property (past_valid && !rst && !$past(rst) |-> out == $past(in));

  // Change propagation: if in changed last cycle and not in reset for two cycles, out changes now to that value
  a_latency_change: assert property (
                      past_valid && $past(past_valid) &&
                      !rst && !$past(rst) && !$past(rst,2) &&
                      ($past(in) != $past(in,2))
                      |-> $changed(out) && out == $past(in)
                    );

  // Out must never be X/Z at sampled times (after we have history)
  a_out_known:      assert property (past_valid |-> !$isunknown(out));

  // While reset remains asserted across consecutive cycles, out stays stable (and zero by a_rst_zero)
  a_rst_stable:     assert property (past_valid && rst && $past(rst) |-> $stable(out));

  // Coverage
  c_reset:          cover  property (rst);
  c_deassert:       cover  property ($fell(rst));
  c_capture_cov:    cover  property (
                      past_valid && $past(past_valid) &&
                      !rst && !$past(rst) && !$past(rst,2) &&
                      ($past(in) != $past(in,2)) && out == $past(in)
                    );

endmodule

// Bind into the DUT
bind BusHold BusHold_sva #(.n(n)) BusHold_sva_i (.clk(clk), .rst(rst), .in(in), .out(out));