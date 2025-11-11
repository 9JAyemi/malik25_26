// SVA for d_ff_async_reset
// Bind example (in testbench): bind d_ff_async_reset d_ff_async_reset_sva sva(.D(D), .RESET_B(RESET_B), .CLK(CLK), .Q(Q));

module d_ff_async_reset_sva (input logic D, RESET_B, CLK, Q);

  // Track if reset was seen since last clock edge
  logic reset_seen;
  initial reset_seen = 1'b0;
  always @(negedge RESET_B or posedge CLK) begin
    if (!RESET_B) reset_seen <= 1'b1;
    else          reset_seen <= 1'b0;
  end

  // Basic sanity: no X on key inputs; Q not X when out of reset
  ap_no_x_inputs:  assert property (@(posedge CLK or negedge RESET_B) !$isunknown({CLK, RESET_B, D}));
  ap_no_x_q:       assert property (@(posedge CLK) RESET_B |-> !$isunknown(Q));

  // Asynchronous reset: when low, Q is 0 and stays 0 until release
  ap_rst_low_holds: assert property (@(posedge CLK or negedge RESET_B)
                                     (!RESET_B) |-> (Q==0 throughout !RESET_B));
  // Also sample at clocks while held in reset
  ap_rst_low_at_clk: assert property (@(posedge CLK) !RESET_B |-> (Q==0));
  // After reset deasserts, Q stays 0 until the next clock edge
  ap_hold_zero_until_clk_after_release: assert property (@(posedge CLK or posedge RESET_B)
                                                         $rose(RESET_B) |-> (Q==0 until_with $rose(CLK)));

  // Functional capture: with no reset seen between consecutive clocks, Q captures prior D
  ap_data_capture: assert property (@(posedge CLK)
                                    (RESET_B && !reset_seen && !$isunknown($past(D)))
                                    |-> (Q == $past(D)));

  // Coverage
  cp_reset_pulse:  cover property (@(posedge CLK or negedge RESET_B) $fell(RESET_B) ##[1:$] $rose(RESET_B));
  cp_cap_0:        cover property (@(posedge CLK) (RESET_B && !reset_seen && $past(D)==1'b0) |-> (Q==1'b0));
  cp_cap_1:        cover property (@(posedge CLK) (RESET_B && !reset_seen && $past(D)==1'b1) |-> (Q==1'b1));

endmodule