// SVA for delay_module
// Bind this checker to the DUT instance(s)
module delay_module_sva;
  // Access DUT signals directly via bind (clk, reset, in_signal, out_signal, buffer)
  default clocking cb @(posedge clk); endclocking

  // Reset clears all state on the next cycle
  ap_reset_clears: assert property (reset |=> (buffer[0]==3'b000 && buffer[1]==3'b000 && buffer[2]==3'b000 && out_signal==1'b0));

  // While reset remains asserted, outputs stay 0
  ap_out_zero_while_reset: assert property ((reset && $past(reset)) |-> out_signal==1'b0);

  // Output stays 0 for 3 cycles after reset deassertion (pipeline flush)
  ap_flush_after_reset: assert property ($fell(reset) |=> out_signal==1'b0[*3]);

  // Shift-register behavior (non-reset consecutive cycles)
  ap_shift_chain: assert property ((!reset && !$past(reset)) |->
                                   (buffer[0] == $past(in_signal)   &&
                                    buffer[1] == $past(buffer[0])   &&
                                    buffer[2] == $past(buffer[1])   &&
                                    out_signal == $past(buffer[2])));

  // Functional 3-cycle delay when no reset in the last 3 cycles
  ap_delay3: assert property ((!reset && !$past(reset,1) && !$past(reset,2) && !$past(reset,3)) |->
                               (out_signal == $past(in_signal,3)));

  // Type/width safety: upper bits of buffer are always 0
  ap_buf0_msb0: assert property (buffer[0][2:1] == 2'b00);
  ap_buf1_msb0: assert property (buffer[1][2:1] == 2'b00);
  ap_buf2_msb0: assert property (buffer[2][2:1] == 2'b00);

  // Output never X once reset has occurred at least once
  logic seen_reset;
  initial seen_reset = 1'b0;
  always @(posedge clk) if (reset) seen_reset <= 1'b1;
  ap_no_x_after_reset: assert property (seen_reset |-> !$isunknown(out_signal));

  // Coverage: rise/fall propagate with 3-cycle latency (no resets during window)
  cp_rise_delay: cover property (($rose(in_signal) && !reset) ##1 !reset ##1 !reset ##1 !reset ##1 $rose(out_signal));
  cp_fall_delay: cover property (($fell(in_signal) && !reset) ##1 !reset ##1 !reset ##1 !reset ##1 $fell(out_signal));
  // Coverage: reset deassertion flush then propagation of next change
  cp_reset_flush: cover property ($fell(reset) ##1 out_signal==1'b0[*3] ##1 $changed(in_signal) ##3 $changed(out_signal));
endmodule

bind delay_module delay_module_sva sva_inst();