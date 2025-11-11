// SVA for synchronizer_flop
module synchronizer_flop_sva #(
  parameter int width = 1,
  parameter logic [width-1:0] reset_val = '0
)(
  input  logic [width-1:0] data_in,
  input  logic             clk_out,
  input  logic [width-1:0] sync_data_out,
  input  logic             async_reset
);

  localparam logic [width-1:0] RESET = reset_val;

  default clocking cb @(posedge clk_out); endclocking

  // Async reset takes effect immediately
  assert property (@(posedge async_reset) ##0 (sync_data_out === RESET));

  // While reset high, output is RESET at clock edges and holds stable across cycles
  assert property (@(posedge clk_out) async_reset |-> ##0 (sync_data_out === RESET));
  assert property (@(posedge clk_out) $past(async_reset) && async_reset |-> ##0 (sync_data_out === RESET && $stable(sync_data_out)));

  // D->Q behavior when not in reset (1-cycle latency)
  assert property (@(posedge clk_out) disable iff (async_reset) ##0 (sync_data_out == $past(data_in)));

  // Output changes only on allowed events (clk or async reset)
  assert property (@($global_clock) $changed(sync_data_out) |-> ($rose(clk_out) || $rose(async_reset)));

  // After reset deasserts, hold RESET until first clk edge
  assert property (@(negedge async_reset) (sync_data_out === RESET) until_with (@(posedge clk_out) 1));

  // No X on output while in reset
  assert property (@(posedge clk_out or posedge async_reset) async_reset |-> ##0 !$isunknown(sync_data_out));

  // Coverage
  cover property (@(posedge async_reset) ##0 (sync_data_out === RESET));
  cover property (@(posedge clk_out) disable iff (async_reset) (data_in != $past(data_in)) && (sync_data_out == $past(data_in)));
  cover property (@(negedge async_reset) ##1 @(posedge clk_out) 1);

endmodule

bind synchronizer_flop
  synchronizer_flop_sva #(.width(width), .reset_val(reset_val))
  synchronizer_flop_sva_i (
    .data_in(data_in),
    .clk_out(clk_out),
    .sync_data_out(sync_data_out),
    .async_reset(async_reset)
  );