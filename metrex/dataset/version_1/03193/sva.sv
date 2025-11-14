module RisingEdgeDetector_sva #(parameter bit CHECK_INTERNAL = 1) (
  input logic clk,
  input logic in,
  input logic out,
  input logic prev_in // bind this to DUT's internal if available; ignored if CHECK_INTERNAL=0
);

  // Safe use of $past without a reset
  logic past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Functional equivalence: out is 1 iff in rose this cycle
  ap_equiv: assert property (out == (in && !$past(in)));

  // Optional internal state checks (bind prev_in)
  if (CHECK_INTERNAL) begin
    ap_prev_tracks_in: assert property (prev_in == $past(in));
    ap_out_matches_internal: assert property (out == (in && !prev_in));
  end

  // Basic X-check on output (after first valid cycle)
  ap_no_x_out: assert property (!$isunknown(out));

  // Coverage
  cv_pulse_on_rise:    cover property ($rose(in) && out);
  cv_no_pulse_on_fall: cover property ($fell(in) && !out);
  cv_stay_high_no_pulse: cover property (in && $past(in) && !out);
  cv_two_pulses_separated: cover property (($rose(in) && out) ##[1:$] ($rose(in) && out));

endmodule

// Example bind (inside a testbench or package):
// bind RisingEdgeDetector RisingEdgeDetector_sva #(.CHECK_INTERNAL(1))
//   sva ( .clk(clk), .in(in), .out(out), .prev_in(prev_in) );