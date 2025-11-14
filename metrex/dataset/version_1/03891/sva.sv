// SVA for binary_counter
module binary_counter_sva (
  input logic        clk,
  input logic        reset,
  input logic        enable,
  input logic        load,
  input logic [3:0]  data_in,
  input logic [3:0]  count
);

  // Async reset behavior
  ap_async_reset_now:  assert property (@(posedge reset) count == 4'h0);
  ap_in_reset_zero:    assert property (@(posedge clk) reset |-> (count == 4'h0));

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Hold when not enabled (regardless of load)
  ap_hold_when_disabled: assert property (!enable |=> count == $past(count));

  // Load when enabled+load
  ap_load_when_enabled:  assert property (enable && load |=> count == data_in);

  // Increment when enabled and not loading (mod-16)
  ap_increment:          assert property (enable && !load |=> count == $past(count) + 4'd1);

  // Load has no effect without enable
  ap_load_gated_by_enable: assert property (!enable && load |=> count == $past(count));

  // Count must be known out of reset
  ap_count_known: assert property (!$isunknown(count));

  // Coverage
  cp_reset:      cover property (@(posedge reset) 1);
  cp_hold:       cover property (!enable |=> count == $past(count));
  cp_load:       cover property (enable && load |=> count == data_in);
  cp_inc:        cover property (enable && !load |=> count == $past(count) + 4'd1);
  cp_wrap:       cover property (count == 4'hF && enable && !load |=> count == 4'h0);
  cp_load_gated: cover property (!enable && load |=> count == $past(count));

endmodule

bind binary_counter binary_counter_sva sva_i (.*);