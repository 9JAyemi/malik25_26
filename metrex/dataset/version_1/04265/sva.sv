// SVA for Counter32
`ifndef COUNTER32_SVA
`define COUNTER32_SVA

module Counter32_sva ();

  // Clocking/reset for assertions
  default clocking cb @(posedge Clk_i); endclocking
  default disable iff (!Reset_n_i);

  // Async reset clears immediately (after NBA)
  always @(negedge Reset_n_i) begin
    #0 assert (Value == '0) else $error("Counter32: Value not cleared on async Reset_n_i");
  end

  // Outputs reflect internal state
  ap_outputs_match: assert property (DH_o == Value[31:16] &&
                                     DL_o == Value[15:0]  &&
                                     Overflow_o == Value[32] &&
                                     Zero_o == (Value[31:0] == 32'd0));

  // Priority: ResetSig > Preset > Enable, next-cycle effects
  ap_resetSig_wins: assert property (ResetSig_i |=> (Value == '0));
  ap_preset_only:   assert property ((!ResetSig_i && Preset_i)
                                    |=> (Value == {1'b0, PresetValH_i, PresetValL_i}));

  // Enable behaviors
  ap_enable_inc: assert property ((!ResetSig_i && !Preset_i && Enable_i && !Direction_i)
                                  |=> (Value == {1'b0, $past(Value[31:0])} + 33'd1));
  ap_enable_dec: assert property ((!ResetSig_i && !Preset_i && Enable_i &&  Direction_i)
                                  |=> (Value == {1'b0, $past(Value[31:0])} - 33'd1));
  ap_hold:       assert property ((!ResetSig_i && !Preset_i && !Enable_i)
                                  |=> (Value == $past(Value)));

  // Wrap/borrow specifics and flag
  ap_inc_wrap: assert property ((!ResetSig_i && !Preset_i && Enable_i && !Direction_i &&
                                 $past(Value[31:0]) == 32'hFFFF_FFFF)
                                |=> (Value[31:0] == 32'h0000_0000 && Overflow_o));
  ap_inc_nowrap_flag: assert property ((!ResetSig_i && !Preset_i && Enable_i && !Direction_i &&
                                        $past(Value[31:0]) != 32'hFFFF_FFFF)
                                       |=> (!Overflow_o));
  ap_dec_wrap: assert property ((!ResetSig_i && !Preset_i && Enable_i && Direction_i &&
                                 $past(Value[31:0]) == 32'h0000_0000)
                                |=> (Value[31:0] == 32'hFFFF_FFFF && Overflow_o));
  ap_dec_nowrap_flag: assert property ((!ResetSig_i && !Preset_i && Enable_i && Direction_i &&
                                        $past(Value[31:0]) != 32'h0000_0000)
                                       |=> (!Overflow_o));

  // Coverage
  cp_async_reset: cover property (@(negedge Reset_n_i) 1);
  cp_sync_reset:  cover property (ResetSig_i ##1 (Value == '0));
  cp_preset:      cover property ((!ResetSig_i && Preset_i) ##1 (Value == {1'b0, PresetValH_i, PresetValL_i}));
  cp_inc:         cover property ((!ResetSig_i && !Preset_i && Enable_i && !Direction_i) ##1 1);
  cp_dec:         cover property ((!ResetSig_i && !Preset_i && Enable_i &&  Direction_i) ##1 1);
  cp_inc_wrap:    cover property ((!ResetSig_i && !Preset_i && Enable_i && !Direction_i &&
                                   $past(Value[31:0]) == 32'hFFFF_FFFF)
                                  ##1 (Overflow_o && {DH_o,DL_o} == 32'h0000_0000));
  cp_dec_wrap:    cover property ((!ResetSig_i && !Preset_i && Enable_i && Direction_i &&
                                   $past(Value[31:0]) == 32'h0000_0000)
                                  ##1 (Overflow_o && {DH_o,DL_o} == 32'hFFFF_FFFF));
  cp_zero_flag:   cover property (Zero_o);

endmodule

bind Counter32 Counter32_sva b0();

`endif