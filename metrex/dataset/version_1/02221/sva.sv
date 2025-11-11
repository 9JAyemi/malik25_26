// SVA for lfsr_count255
// Focused, high-quality checks with concise coverage

module lfsr_count255_sva (
  input logic        i_sys_clk,
  input logic        i_sys_rst,
  input logic [7:0]  lfsr_reg_i,
  input logic        o_lfsr_256_done,
  input logic        lfsr_d0_i,
  input logic        lfsr_256_equal_i
);

  default clocking cb @(posedge i_sys_clk); endclocking

  // Async reset should clear immediately
  ap_async_reset_immediate: assert property (@(posedge i_sys_rst)
    1 |-> (lfsr_reg_i == 8'h00 && o_lfsr_256_done == 1'b0));

  // Hold in reset
  ap_hold_in_reset: assert property (cb i_sys_rst |-> (lfsr_reg_i == 8'h00 && o_lfsr_256_done == 1'b0));

  // No unknowns after reset deasserted
  ap_no_x: assert property (cb !i_sys_rst |-> !$isunknown({lfsr_reg_i, o_lfsr_256_done, lfsr_d0_i, lfsr_256_equal_i}));

  // Combinational correctness
  ap_d0_func:    assert property (cb lfsr_d0_i == ~^{lfsr_reg_i[7], lfsr_reg_i[5], lfsr_reg_i[4], lfsr_reg_i[3]});
  ap_equal_func: assert property (cb lfsr_256_equal_i == (lfsr_reg_i == 8'hFF));

  // Output definition
  ap_done_matches_equal: assert property (cb !i_sys_rst |-> (o_lfsr_256_done == lfsr_256_equal_i));

  // Next-state logic
  ap_next_shift: assert property (cb disable iff (i_sys_rst)
    !$past(i_sys_rst) && !$past(lfsr_256_equal_i)
      |-> lfsr_reg_i == { $past(lfsr_reg_i[6:0]), $past(lfsr_d0_i) });

  ap_next_wrap: assert property (cb disable iff (i_sys_rst)
    !$past(i_sys_rst) &&  $past(lfsr_256_equal_i)
      |-> lfsr_reg_i == 8'h00);

  // Done is a single-cycle pulse and followed by 0 state
  ap_done_pulse: assert property (cb disable iff (i_sys_rst) o_lfsr_256_done |=> !o_lfsr_256_done);
  ap_done_to_zero: assert property (cb disable iff (i_sys_rst) o_lfsr_256_done |=> (lfsr_reg_i == 8'h00));

  // First step after reset release should be 0x01 (since taps all 0 => d0=1)
  ap_first_step: assert property (cb $fell(i_sys_rst) |=> lfsr_reg_i == 8'h01);

  // Coverage: observe wrap FF->00 and pulse
  cp_reach_ff_and_wrap: cover property (cb disable iff (i_sys_rst)
    (lfsr_reg_i == 8'h00) ##[1:260] (lfsr_reg_i == 8'hFF && o_lfsr_256_done) ##1 (lfsr_reg_i == 8'h00 && !o_lfsr_256_done));

endmodule

bind lfsr_count255 lfsr_count255_sva u_lfsr_count255_sva (
  .i_sys_clk(i_sys_clk),
  .i_sys_rst(i_sys_rst),
  .lfsr_reg_i(lfsr_reg_i),
  .o_lfsr_256_done(o_lfsr_256_done),
  .lfsr_d0_i(lfsr_d0_i),
  .lfsr_256_equal_i(lfsr_256_equal_i)
);