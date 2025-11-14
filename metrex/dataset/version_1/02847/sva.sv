// SVA for uart_sync_flops
// Bind these assertions to the DUT; concise but full functional checks and coverage.

module uart_sync_flops_sva #(
  parameter int width = 1,
  parameter bit init_value = 1'b0
)(
  input                   rst_i,
  input                   clk_i,
  input                   stage1_rst_i,
  input                   stage1_clk_en_i,
  input  [width-1:0]      async_dat_i,
  input  [width-1:0]      sync_dat_o
);
  // Access to internal flop_0 is resolved in bound scope
  // function for init vector
  function automatic [width-1:0] init_vec; init_vec = {width{init_value}}; endfunction

  // Parameter sanity
  initial assert (width >= 1) else $fatal(1, "%m width must be >= 1");

  // Async reset immediately drives both flops to init at rst edge
  assert property (@(posedge rst_i) ##0 (flop_0 == init_vec() && sync_dat_o == init_vec()))
    else $error("%m async reset failed to set init");

  // While in reset at clk edge, hold at init
  assert property (@(posedge clk_i) rst_i |-> (flop_0 == init_vec() && sync_dat_o == init_vec()));

  // Stage-1 flop always captures async input on clk when out of reset
  assert property (@(posedge clk_i) disable iff (rst_i)
                   $past(!rst_i) |-> (flop_0 == $past(async_dat_i)));

  // stage1_rst_i has priority over enable
  assert property (@(posedge clk_i) disable iff (rst_i)
                   stage1_rst_i |-> (sync_dat_o == init_vec()));

  // Enable transfers from flop_0; otherwise hold
  assert property (@(posedge clk_i) disable iff (rst_i)
                   (!stage1_rst_i && stage1_clk_en_i) |-> (sync_dat_o == $past(flop_0)));
  assert property (@(posedge clk_i) disable iff (rst_i)
                   (!stage1_rst_i && !stage1_clk_en_i) |-> (sync_dat_o == $past(sync_dat_o)));

  // No X on key state/control when not in reset
  assert property (@(posedge clk_i) disable iff (rst_i)
                   !$isunknown(stage1_clk_en_i) && !$isunknown(stage1_rst_i) &&
                   !$isunknown(flop_0) && !$isunknown(sync_dat_o));

  // Coverage: async reset, stage1 reset, enable transfer, hold, output edges
  cover property (@(posedge rst_i) ##0 (flop_0 == init_vec() && sync_dat_o == init_vec()));
  cover property (@(posedge clk_i) disable iff (rst_i) stage1_rst_i);
  cover property (@(posedge clk_i) disable iff (rst_i)
                  (!stage1_rst_i && stage1_clk_en_i && !$isunknown(async_dat_i)));
  cover property (@(posedge clk_i) disable iff (rst_i)
                  (!stage1_rst_i && !stage1_clk_en_i)[*3]);
  cover property (@(posedge clk_i) disable iff (rst_i)
                  (!stage1_rst_i && stage1_clk_en_i && $rose(sync_dat_o[0])));
  cover property (@(posedge clk_i) disable iff (rst_i)
                  (!stage1_rst_i && stage1_clk_en_i && $fell(sync_dat_o[0])));
endmodule

bind uart_sync_flops uart_sync_flops_sva #(.width(width), .init_value(init_value)) u_uart_sync_flops_sva (.*);