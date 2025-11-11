// SVA for velocityControlHdl_Reset_Delay
module velocityControlHdl_Reset_Delay_sva;

  default clocking cb @(posedge CLK_IN); endclocking

  // Constants are always zero
  assert property (Constant1_out1 == 32'sd0);
  assert property (Constant_out1  == 32'sd0);

  // Combinational muxes
  assert property (Reset_1 == 1'b0 |-> Reset_Switch1_out1 == In);
  assert property (Reset_1 == 1'b1 |-> Reset_Switch1_out1 == 32'sd0);
  assert property (Reset_1 == 1'b0 |-> Reset_Switch_out1  == In_Delay_out1);
  assert property (Reset_1 == 1'b1 |-> Reset_Switch_out1  == 32'sd0);

  // Out equals mux output
  assert property (Out == Reset_Switch_out1);

  // Synchronous reset on the delay flop
  assert property (reset |=> In_Delay_out1 == 32'sd0);

  // Enable/load and hold behavior of delay flop
  assert property (!reset && enb_1_2000_0  |=> In_Delay_out1 == $past(Reset_Switch1_out1));
  assert property (!reset && !enb_1_2000_0 |=> In_Delay_out1 == $past(In_Delay_out1));

  // When Reset_1=1 and enabled, the delay captures zero
  assert property (!reset && enb_1_2000_0 && Reset_1==1'b1 |=> In_Delay_out1 == 32'sd0);

  // End-to-end: one-cycle path from In to Out when Reset_1=0 (both cycles), enabled, and not in reset
  assert property (!reset && $past(!reset) &&
                   $past(enb_1_2000_0) &&
                   $past(Reset_1==1'b0) && (Reset_1==1'b0)
                   |-> Out == $past(In));

  // X-safety when controls are known
  assert property (!$isunknown({reset,enb_1_2000_0,Reset_1,In}) |-> !$isunknown({Out,In_Delay_out1}));

  // Coverage
  cover property (reset ##1 !reset); // reset release
  cover property (!reset && enb_1_2000_0 && Reset_1==1'b0 ##1 Out == $past(In)); // capture path
  cover property (!reset && !enb_1_2000_0 && $past(Reset_1==1'b0) && Reset_1==1'b0 ##1 Out == $past(Out)); // hold path
  cover property (!reset && enb_1_2000_0 && Reset_1==1'b1 ##1 Out == 32'sd0); // zeroing via Reset_1

endmodule

bind velocityControlHdl_Reset_Delay velocityControlHdl_Reset_Delay_sva sva_inst();