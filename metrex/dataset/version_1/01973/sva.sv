// SVA checker for spis
// Bind this to the DUT to verify behavior across clk, SCLK, SSbar, rd, rst.
module spis_sva (
  input clk,
  input rst,
  input SCLK,
  input SSbar,
  input MOSI,
  input rd,
  input [7:0] dout,
  input data_present,
  input data_present_temp,
  input clear
);

  // Reset effects (after NBA of the reset edge)
  a_reset_effects: assert property (@(posedge rst) ##0 (dout==8'h00 && data_present==1'b0 && clear==1'b1));

  // clear should reflect (rst || rd) after the clk edge update
  a_clear_eq_func: assert property (@(posedge clk) 1'b1 |-> ##0 (clear == (rst || rd)));

  // data_present should equal data_present_temp sampled on this clk edge (after NBA)
  a_dp_follows_temp: assert property (@(posedge clk) disable iff (rst) ##0 (data_present == data_present_temp));

  // Rising clear forces data_present_temp low immediately
  a_dpt_on_clear: assert property (@(posedge clear) ##0 (data_present_temp==1'b0));

  // SSbar rising sets data_present_temp unless clear is high at that instant
  a_dpt_on_ss_rise: assert property (@(posedge SSbar) ##0 (clear ? (data_present_temp==1'b0) : (data_present_temp==1'b1)));

  // After SSbar rise (and not clear), data_present must assert on the next clk sample (same clk tick if SSbar rose between clk edges)
  a_dp_assert_after_ss: assert property (@(posedge clk) disable iff (rst) ($rose(SSbar) && !clear) |-> data_present);

  // If SSbar rises while clear is high, data_present must be 0 at that clk sample
  a_dp_blocked_by_clear: assert property (@(posedge clk) disable iff (rst) ($rose(SSbar) && clear) |-> !data_present);

  // data_present can only rise due to an SSbar rise
  a_dp_rise_implies_ss: assert property (@(posedge clk) disable iff (rst) $rose(data_present) |-> $rose(SSbar));

  // Shift behavior on SCLK: shift only when SSbar low and data not yet present
  a_dout_shift: assert property (@(posedge SCLK) disable iff (rst)
                                 (SSbar==1'b0 && !data_present)
                                 |-> (dout == {$past(dout)[6:0], MOSI}));

  // Hold behavior on SCLK when not shifting (SSbar high or data already present)
  a_dout_hold: assert property (@(posedge SCLK) disable iff (rst)
                                (SSbar==1'b1 || data_present)
                                |-> (dout == $past(dout)));

  // data_present must clear on the clk edge following a clear rise
  a_dp_clears_on_clear: assert property (@(posedge clk) $rose(clear) |-> (data_present==1'b0));

  // Simple X-prop guards on outputs
  a_no_x_dout: assert property (@(posedge SCLK or posedge rst) !$isunknown(dout));
  a_no_x_dp:   assert property (@(posedge clk or posedge rst)   !$isunknown(data_present));

  // Coverage: 8 shifts while selected, SSbar rise, data_present set, then rd clears
  c_8shifts_then_ss: cover property (@(posedge SCLK) disable iff (rst)
                                     (SSbar==1'b0 && !data_present)[*8] ##1 $rose(SSbar));
  c_present_sync:    cover property (@(posedge clk)  disable iff (rst)
                                     $rose(SSbar) ##1 data_present);
  c_read_clears:     cover property (@(posedge clk)  disable iff (rst)
                                     data_present ##1 rd ##1 !data_present);

endmodule

// Bind to DUT (connect internal signals)
bind spis spis_sva u_spis_sva (
  .clk(clk),
  .rst(rst),
  .SCLK(SCLK),
  .SSbar(SSbar),
  .MOSI(MOSI),
  .rd(rd),
  .dout(dout),
  .data_present(data_present),
  .data_present_temp(data_present_temp),
  .clear(clear)
);