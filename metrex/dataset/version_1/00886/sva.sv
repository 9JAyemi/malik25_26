// SVA for arriaiigz_lvds_tx_parallel_register
// Concise checks for reset, load, hold, and change qualification, plus basic coverage.

module arriaiigz_lvds_tx_parallel_register_sva (
  input clk,
  input enable,
  input [3:0] datain,
  input devclrn,
  input devpor,
  input [3:0] dataout
);
  wire rst_n = devpor & devclrn;

  default clocking cb @(posedge clk); endclocking

  // Reset clears output and has priority over enable
  a_reset_clears:         assert property ( !rst_n |-> ##0 (dataout == 4'b0) );
  a_reset_over_enable:    assert property ( (!rst_n && enable) |-> ##0 (dataout == 4'b0) );

  // Load on enable when not in reset
  a_load_on_enable:       assert property ( rst_n && enable |-> ##0 (dataout == datain) );

  // Hold when disabled (no write when enable=0)
  a_hold_when_disabled:   assert property ( rst_n && !enable |-> $stable(dataout) );

  // Output changes only allowed with enable (excluding reset cycles)
  a_change_requires_en:   assert property ( disable iff (!rst_n) $changed(dataout) |-> enable );

  // After reset release with enable low, hold zero until first enable
  a_hold_zero_until_en:   assert property ( $rose(rst_n) && !enable |-> (dataout == 4'b0) until_with enable );

  // Out of reset, dataout should not be X/Z
  a_no_x_out_of_reset:    assert property ( disable iff (!rst_n) !$isunknown(dataout) );

  // Coverage
  c_reset_seen:           cover property ( !rst_n );
  c_enable_load:          cover property ( rst_n && enable && ##0 (dataout == datain) );
  c_hold_cycle:           cover property ( rst_n && !enable && $stable(dataout) );
  c_reset_hold_then_load: cover property ( !rst_n ##1 (rst_n && !enable)[*1:$] ##1 (rst_n && enable) );
endmodule

bind arriaiigz_lvds_tx_parallel_register arriaiigz_lvds_tx_parallel_register_sva
(
  .clk(clk),
  .enable(enable),
  .datain(datain),
  .devclrn(devclrn),
  .devpor(devpor),
  .dataout(dataout)
);