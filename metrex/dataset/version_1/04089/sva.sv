// SVA for data_store: concise, high-quality checks and coverage
module data_store_sva (
  input logic         clk,
  input logic         enable,
  input logic [15:0]  data_in,
  input logic [15:0]  data_out
);

  default clocking @(posedge clk); endclocking
  // valid after first sampled clock
  let past_valid = $past(1'b1);

  // Control signal should never be X/Z after first cycle
  a_enable_known: assert property (past_valid |-> !$isunknown(enable));

  // Capture on enable: known data
  a_capture_known: assert property (
    disable iff (!past_valid)
    enable && !$isunknown($past(data_in)) |-> data_out == $past(data_in)
  );

  // Capture on enable: unknown data propagates to output
  a_capture_unknown: assert property (
    disable iff (!past_valid)
    enable &&  $isunknown($past(data_in)) |-> $isunknown(data_out)
  );

  // Hold when disabled
  a_hold: assert property (
    disable iff (!past_valid)
    !enable |-> (data_out === $past(data_out))
  );

  // Any change to data_out must be due to prior enable
  a_change_requires_enable: assert property (
    disable iff (!past_valid)
    $changed(data_out) |-> $past(enable)
  );

  // Coverage
  c_capture:    cover property (disable iff (!past_valid) enable && !$isunknown($past(data_in)) && data_out == $past(data_in));
  c_hold2:      cover property (disable iff (!past_valid) !enable[*2]);
  c_back2back:  cover property (disable iff (!past_valid) enable ##1 (enable && $changed(data_out)));
  c_blocked_di: cover property (disable iff (!past_valid) !enable && $changed(data_in));

endmodule

// Bind into the DUT (instance or module)
bind data_store data_store_sva i_data_store_sva (.*);