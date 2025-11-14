// SVA for DUC: bindable checker that verifies interpolation, filter/update pipeline, and reset behavior
module DUC_sva #(
  parameter int INPUT_WIDTH = 8,
  parameter int OUTPUT_WIDTH = 8,
  parameter int INTERPOLATION_FACTOR = 4
) ();

  // This checker is intended to be bound into DUC; it refers to DUT internals directly:
  // bind DUC DUC_sva #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH), .INTERPOLATION_FACTOR(INTERPOLATION_FACTOR)) DUC_sva_i();

  default clocking cb @(posedge clk); endclocking

  // Basic sanity on parameterization
  initial assert (INTERPOLATION_FACTOR >= 1)
    else $error("INTERPOLATION_FACTOR must be >= 1");

  // Past-valid helper to gate $past usage
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  // Width used by the adder in filtered_signal computation (per SV sizing rules)
  localparam int SUMW = (INPUT_WIDTH > OUTPUT_WIDTH) ? INPUT_WIDTH : OUTPUT_WIDTH;

  // Reset behavior
  assert property (reset |-> (i_count == 0
                           && interpolated_signal == {INPUT_WIDTH{1'b0}}
                           && out_signal == {OUTPUT_WIDTH{1'b0}}));

  // i_count is always within range [0, INTERPOLATION_FACTOR-1]
  assert property (past_valid |-> (i_count >= 0 && i_count <= INTERPOLATION_FACTOR-1));

  // i_count next-state
  assert property (past_valid && !$past(reset) && ($past(i_count) < INTERPOLATION_FACTOR-1)
                   |-> i_count == $past(i_count) + 1);
  assert property (past_valid && !$past(reset) && ($past(i_count) >= INTERPOLATION_FACTOR-1)
                   |-> i_count == 0);

  // Interpolated-signal behavior (zero stuffing then real sample)
  assert property (past_valid && !$past(reset) && ($past(i_count) < INTERPOLATION_FACTOR-1)
                   |-> interpolated_signal == {INPUT_WIDTH{1'b0}});
  assert property (past_valid && !$past(reset) && ($past(i_count) >= INTERPOLATION_FACTOR-1)
                   |-> interpolated_signal == $past(in_signal));

  // Filter pipeline: filtered_signal uses previous interpolated_signal and out_signal
  assert property (past_valid
                   && !$isunknown($past(interpolated_signal))
                   && !$isunknown($past(out_signal))
                   |-> filtered_signal
                       == ( ( { {SUMW-INPUT_WIDTH{1'b0}}, $past(interpolated_signal) }
                            + { {SUMW-OUTPUT_WIDTH{1'b0}}, $past(out_signal) } ) >> 1 ) [OUTPUT_WIDTH-1:0]);

  // Output pipeline: out_signal is bitwise inversion of previous filtered_signal when not in reset
  assert property (past_valid && !reset && !$isunknown($past(filtered_signal))
                   |-> out_signal == ~ $past(filtered_signal));

  // Functional coverage: observe a full interpolation period (sample -> zeros*(F-1) -> sample)
  cover property (disable iff (reset)
                  past_valid && ($past(i_count) >= INTERPOLATION_FACTOR-1)
                  ##1 (interpolated_signal == {INPUT_WIDTH{1'b0}})[* (INTERPOLATION_FACTOR-1)]
                  ##1 (interpolated_signal == $past(in_signal, INTERPOLATION_FACTOR)));

  // Coverage: i_count cycles 0 -> (nonzero)*(F-1) -> 0
  cover property (disable iff (reset)
                  (i_count == 0) ##1 (i_count != 0)[* (INTERPOLATION_FACTOR-1)] ##1 (i_count == 0));

  // Coverage: reset edges
  cover property ($rose(reset));
  cover property ($fell(reset));

endmodule

// Example bind (place in a testbench or a package included by the testbench):
// bind DUC DUC_sva #(.INPUT_WIDTH(INPUT_WIDTH), .OUTPUT_WIDTH(OUTPUT_WIDTH), .INTERPOLATION_FACTOR(INTERPOLATION_FACTOR)) DUC_sva_i();