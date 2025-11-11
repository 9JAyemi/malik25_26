// SVA for rising_edge_detection
// Bind into DUT to check behavior and provide concise coverage

bind rising_edge_detection rising_edge_detection_sva i_rising_edge_detection_sva (.*);

module rising_edge_detection_sva (
  input clk,
  input reset,
  input [7:0] data,
  input match,
  input [7:0] prev_data
);

  // Reset values held low
  assert property (@(posedge clk) reset |-> (match == 1'b0 && prev_data == 8'h00))
    else $error("RESET: match/prev_data not cleared");

  // Core function: match indicates strict increase vs previous sample (uses old prev_data)
  assert property (@(posedge clk) !reset |-> (match == (data > prev_data)))
    else $error("FUNC: match != (data > prev_data)");

  // State pipeline: after two consecutive non-reset cycles, prev_data mirrors prior data
  sequence two_clean_cycles; !reset ##1 !reset; endsequence
  assert property (@(posedge clk) two_clean_cycles |-> (prev_data == $past(data)))
    else $error("STATE: prev_data != $past(data)");

  // No X/Z when active
  assert property (@(posedge clk) !reset |-> (!$isunknown(data) && !$isunknown({match, prev_data})))
    else $error("XCHK: Unknown on data/match/prev_data when active");

  // Coverage: reset release and all compare outcomes
  cover property (@(posedge clk) $fell(reset));
  cover property (@(posedge clk) !reset && (data > prev_data) && match);  // increase detected
  cover property (@(posedge clk) !reset && (data == prev_data) && !match); // equal
  cover property (@(posedge clk) !reset && (data < prev_data) && !match);  // decrease

endmodule