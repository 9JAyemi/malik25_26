// SVA for altera_tse_false_path_marker
module altera_tse_false_path_marker_sva #(
  parameter int MARKER_WIDTH = 1
)(
  input  logic                     reset,
  input  logic                     clk,
  input  logic [MARKER_WIDTH-1:0]  data_in,
  input  logic [MARKER_WIDTH-1:0]  data_out
);

  // Static parameter check
  initial assert (MARKER_WIDTH >= 1)
    else $error("MARKER_WIDTH must be >= 1");

  // Async reset must clear output immediately on reset edge
  property p_async_clear_now;
    @(posedge reset) ##0 (data_out == '0);
  endproperty
  assert property (p_async_clear_now);

  // While reset is asserted, output must be zero at each clk edge
  property p_hold_zero_during_reset;
    @(posedge clk) reset |-> (data_out == '0);
  endproperty
  assert property (p_hold_zero_during_reset);

  // Register behavior: output equals previous cycle input (skip cycles adjacent to reset)
  property p_next_cycle_capture;
    @(posedge clk) (!reset && !$past(reset)) |-> (data_out == $past(data_in));
  endproperty
  assert property (p_next_cycle_capture);

  // If input is stable across cycles, output stays stable across cycles (no spurious updates)
  property p_stable_if_in_stable;
    @(posedge clk) disable iff (reset)
      (data_in == $past(data_in)) |-> (data_out == $past(data_out));
  endproperty
  assert property (p_stable_if_in_stable);

  // Output changes only on posedge clk or posedge reset (no glitches)
  property p_out_changes_only_on_clk_or_rst;
    @(posedge clk or posedge reset or data_out)
      $changed(data_out) |-> ($rose(clk) || $rose(reset));
  endproperty
  assert property (p_out_changes_only_on_clk_or_rst);

  // No X/Z on output when out of reset
  property p_no_x_out_of_reset;
    @(posedge clk) !reset |-> !$isunknown(data_out);
  endproperty
  assert property (p_no_x_out_of_reset);

  // Coverage: reset assert/deassert and data propagation
  cover property (@(posedge reset) 1);
  cover property (@(posedge clk) $fell(reset));
  cover property (@(posedge clk) disable iff (reset)
                  $changed(data_in) ##1 (data_out == $past(data_in)));

endmodule

// Bind into DUT
bind altera_tse_false_path_marker
  altera_tse_false_path_marker_sva #(.MARKER_WIDTH(MARKER_WIDTH))
  altera_tse_false_path_marker_sva_i (
    .reset   (reset),
    .clk     (clk),
    .data_in (data_in),
    .data_out(data_out)
  );