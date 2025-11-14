// SVA for dff_counter
module dff_counter_sva(
  input        clk,
  input        reset,       // active-low synchronous reset: 0=reset, 1=run
  input  [3:0] count,
  input  [3:0] counter,
  input [11:0] dff_array
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior: seed and clear visible next cycle, hold stable under held reset
  ap_reset_seed:  assert property (!reset |=> (counter==4'h0 && dff_array==12'h5A5));
  ap_reset_hold:  assert property (!reset && $past(!reset) |-> (counter==4'h0 && dff_array==12'h5A5 && count==$past(count)));

  // Normal operation: counter increments, count lags counter by 1, shifter shifts in 0
  ap_cnt_inc:     assert property (disable iff (!reset) counter == $past(counter) + 4'd1);
  ap_count_lags:  assert property (disable iff (!reset) count   == $past(counter));
  ap_shift:       assert property (disable iff (!reset) dff_array == { $past(dff_array[10:0]), 1'b0 });

  // Wrap-around check for counter
  ap_cnt_wrap:    assert property (disable iff (!reset) ($past(counter)==4'hF) |-> (counter==4'h0));

  // No X/Z during normal operation
  ap_no_x:        assert property (disable iff (!reset) !$isunknown({counter, count, dff_array}));

  // (Redundant but explicit) LSB forced to 0 in run mode
  ap_lsb_zero:    assert property (disable iff (!reset) dff_array[0]==1'b0);

  // Coverage
  cp_reset_deassert: cover property ($rose(reset));
  cp_cnt_wrap:       cover property (disable iff (!reset) (counter==4'hF) ##1 (counter==4'h0));
  cp_shift_to_zero:  cover property ($rose(reset) ##12 (dff_array==12'h000));
endmodule

bind dff_counter dff_counter_sva sva_i(.clk(clk), .reset(reset), .count(count), .counter(counter), .dff_array(dff_array));