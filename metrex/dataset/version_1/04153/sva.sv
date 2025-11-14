// SVA for CDC_Synchronizer
// Checks pipeline correctness, end-to-end latency, X-safety, and provides concise coverage.

module CDC_Synchronizer_sva #(parameter int N = 8) (
  input logic               clk_out,
  input logic [N-1:0]       data_in,
  input logic               rst_in,
  input logic [N-1:0]       data_out,
  input logic               rst_out,
  input logic [N-1:0]       synchronized_data,
  input logic [N-1:0]       latched_data,
  input logic               synchronized_reset,
  input logic               latched_reset
);

  default clocking cb @(posedge clk_out); endclocking

  // Basic wiring to outputs
  assert property (data_out == latched_data)
    else $error("data_out must mirror latched_data");
  assert property (rst_out == latched_reset)
    else $error("rst_out must mirror latched_reset");

  // Stage-1 register behavior
  assert property (disable iff ($initstate)
                   synchronized_data == $past(data_in))
    else $error("Stage-1 data sync mismatch: sync_data != $past(data_in)");
  assert property (disable iff ($initstate)
                   synchronized_reset == $past(rst_in))
    else $error("Stage-1 reset sync mismatch: sync_rst != $past(rst_in)");

  // Stage-2 register behavior
  assert property (disable iff ($initstate)
                   latched_data == $past(synchronized_data))
    else $error("Stage-2 data latch mismatch: latched_data != $past(sync_data)");
  assert property (disable iff ($initstate)
                   latched_reset == $past(synchronized_reset))
    else $error("Stage-2 reset latch mismatch: latched_rst != $past(sync_rst)");

  // End-to-end 2-cycle latency (from input sample to output)
  assert property (disable iff ($initstate || $past($initstate))
                   data_out == $past(data_in,2))
    else $error("E2E data latency violation: data_out != $past(data_in,2)");
  assert property (disable iff ($initstate || $past($initstate))
                   rst_out == $past(rst_in,2))
    else $error("E2E reset latency violation: rst_out != $past(rst_in,2)");

  // X-propagation safety under known/stable inputs
  assert property (disable iff ($initstate || $past($initstate))
                   !$isunknown($past(data_in,2)) |-> !$isunknown(data_out))
    else $error("data_out became X with known data_in history");
  assert property (disable iff ($initstate || $past($initstate))
                   !$isunknown($past(rst_in,2)) |-> !$isunknown(rst_out))
    else $error("rst_out became X with known rst_in history");

  // Coverage: observe propagation of data and reset edges through the 2-stage sync
  cover property ($changed(data_in) ##2 (data_out == $past(data_in,2)));
  cover property ($rose(rst_in)     ##2 $rose(rst_out));
  cover property ($fell(rst_in)     ##2 $fell(rst_out));

  // Coverage: multi-bit change snapshot propagates
  cover property (((data_in ^ $past(data_in)) != '0) ##2 (data_out == $past(data_in,2)));

endmodule

// Bind into DUT (connects to ports and internal regs by name)
bind CDC_Synchronizer CDC_Synchronizer_sva #(.N(N)) u_cdc_sva (.*);