// SVA for module register
// Bind this file to the DUT; focuses on concise, high-quality checks and coverage.

module register_sva (
  input clk,
  input reset,          // active-low
  input load,
  input [3:0] data_in,
  input [3:0] data_out,
  input [3:0] reg_data  // internal
);

  default clocking cb @ (posedge clk); endclocking

  // Basic consistency
  a_dataout_matches_reg: assert property (cb data_out == reg_data);

  // Asynchronous reset must clear immediately
  a_async_reset_clear: assert property (@(negedge reset) 1'b1 |-> ##0 (reg_data == 4'h0 && data_out == 4'h0));

  // During reset, output held at zero
  a_hold_zero_in_reset: assert property (cb !reset |-> data_out == 4'h0);

  // Load updates register on next clock
  a_load_updates: assert property (cb disable iff (!reset) load |=> data_out == $past(data_in));

  // No load holds prior value
  a_hold_when_no_load: assert property (cb disable iff (!reset) !load |=> data_out == $past(data_out));

  // Known-value checks
  a_known_reset: assert property (cb !$isunknown(reset));
  a_known_ctrl:  assert property (cb disable iff (!reset) !$isunknown(load));
  a_known_when_load: assert property (cb disable iff (!reset) load |-> !$isunknown(data_in));
  a_known_out:   assert property (cb !$isunknown(data_out));

  // Coverage
  c_reset_assert:     cover property (@(negedge reset) 1'b1);
  c_reset_release:    cover property (cb $rose(reset));
  c_one_load:         cover property (cb disable iff (!reset) load ##1 (data_out == $past(data_in)));
  c_hold_cycle:       cover property (cb disable iff (!reset) !load ##1 (data_out == $past(data_out)));
  c_two_distinct_loads: cover property (cb disable iff (!reset)
                                        load ##1 (data_out == $past(data_in))
                                        ##[1:$] load && (data_in != $past(data_out))
                                        ##1 (data_out == $past(data_in)));
  c_any_toggle:       cover property (cb disable iff (!reset) $changed(data_out));

endmodule

bind register register_sva u_register_sva(
  .clk(clk),
  .reset(reset),
  .load(load),
  .data_in(data_in),
  .data_out(data_out),
  .reg_data(reg_data)
);