// SVA for shift_register
module shift_register_sva;
  default clocking cb @(posedge CLK); endclocking

  // Functional decode
  ap_shift_data_decode: assert property (shift_data == (mode ? 16'hFFFF : 16'h0000));

  // LOAD behavior (and priority over SHIFT)
  ap_load: assert property (LOAD |=> shift_cnt==0
                                  && shift_reg[0]==$past(DATA_IN)
                                  && shift_reg[1]==$past(shift_data)
                                  && shift_reg[2]==$past(shift_data)
                                  && shift_reg[3]==$past(shift_data));

  // SHIFT behavior (when not loading)
  ap_shift: assert property (SHIFT && !LOAD |=> shift_reg[0]==$past(shift_reg[1])
                                         && shift_reg[1]==$past(shift_reg[2])
                                         && shift_reg[2]==$past(shift_reg[3])
                                         && shift_reg[3]==$past(shift_data)
                                         && shift_cnt==$past(shift_cnt)+1);

  // Hold when idle
  ap_hold: assert property (!LOAD && !SHIFT |=> $stable(shift_reg[0]) && $stable(shift_reg[1])
                                           && $stable(shift_reg[2]) && $stable(shift_reg[3])
                                           && $stable(shift_cnt));

  // Start tracking after first LOAD
  bit loaded;
  initial loaded = 1'b0;
  always @(posedge CLK) if (LOAD) loaded <= 1'b1;

  // Counter must stay within bounds once initialized
  ap_cnt_in_range: assert property (loaded |-> (shift_cnt inside {[0:3]}));

  // Forbid shifting past last valid index (catches overflow bug)
  ap_no_shift_at_max: assert property (loaded && SHIFT && !LOAD |-> $past(shift_cnt) < 3);

  // DATA_OUT must reflect selected entry when index is valid
  ap_data_out_mux: assert property ((shift_cnt inside {[0:3]}) |-> (DATA_OUT == shift_reg[shift_cnt]));

  // Mode known whenever used
  ap_mode_known_when_used: assert property ((LOAD || SHIFT) |-> !$isunknown(mode));

  // Coverage
  cp_load0: cover property (LOAD && mode==1'b0);
  cp_load1: cover property (LOAD && mode==1'b1);
  cp_shift: cover property (SHIFT && !LOAD);
  cp_load_then_3_shift: cover property (LOAD ##1 (SHIFT && !LOAD)[*3]);
  cp_priority: cover property (LOAD && SHIFT);
  cp_reach_cnt3: cover property (LOAD ##1 (SHIFT && !LOAD)[*3] ##1 (shift_cnt==3));
endmodule

bind shift_register shift_register_sva sva_inst();