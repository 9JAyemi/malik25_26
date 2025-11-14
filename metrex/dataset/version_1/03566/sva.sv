// SVA for util_delay: concise, high-quality checks and coverage

module util_delay_sva #(
  parameter int DATA_WIDTH   = 1,
  parameter int DELAY_CYCLES = 1
) (
  input  logic                  clk,
  input  logic                  reset,
  input  logic                  din,
  input  logic [DATA_WIDTH-1:0] dout
);

  default clocking cb @(posedge clk); endclocking

  // Parameter sanity
  initial begin
    assert (DATA_WIDTH   >= 1) else $error("util_delay: DATA_WIDTH must be >=1");
    assert (DELAY_CYCLES >= 1) else $error("util_delay: DELAY_CYCLES must be >=1");
  end

  // Basic hygiene
  a_reset_known:  assert property (! $isunknown(reset));

  // While reset is asserted, output must be zeroed
  a_reset_zero:   assert property (reset |-> (dout == '0));

  // Define a clean window with no reset for DELAY_CYCLES+1 clocks (enables safe $past)
  sequence s_no_reset_win;
    (!reset)[*DELAY_CYCLES+1];
  endsequence

  // End-to-end delay correctness (after a clean no-reset window)
  a_delay_ok:     assert property (s_no_reset_win |-> (dout == $past(din, DELAY_CYCLES)));

  // No X on dout during active operation windows
  a_no_x_dout:    assert property (s_no_reset_win |-> ! $isunknown(dout));

  // With 1-bit din driving wider dout, upper bits must remain zero (by design)
  generate if (DATA_WIDTH > 1) begin
    a_upper_zero: assert property (s_no_reset_win |-> (dout[DATA_WIDTH-1:1] == '0));
  end endgenerate

  // Functional coverage
  c_reset_pulse:  cover property (reset ##1 !reset);
  c_rise_delay:   cover property (s_no_reset_win and $rose(din) ##DELAY_CYCLES (dout == $past(din, DELAY_CYCLES)));
  c_fall_delay:   cover property (s_no_reset_win and $fell(din) ##DELAY_CYCLES (dout == $past(din, DELAY_CYCLES)));

endmodule

// Bind into the DUT
bind util_delay util_delay_sva #(
  .DATA_WIDTH(DATA_WIDTH),
  .DELAY_CYCLES(DELAY_CYCLES)
) util_delay_sva_b (
  .clk  (clk),
  .reset(reset),
  .din  (din),
  .dout (dout)
);