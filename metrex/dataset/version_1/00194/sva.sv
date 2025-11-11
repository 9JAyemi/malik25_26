// SystemVerilog Assertions for Bus_Arbiter
// Bind these to the DUT. Focused, high-quality checks and coverage.

module Bus_Arbiter_sva;

  // Use DUT scope (via bind) and its clock/reset
  default clocking cb @(posedge Clock_in); endclocking
  default disable iff (Reset_in);

  // Shorthand predicates
  let inst_act = (Inst_Read_in || Inst_Write_in);
  let data_act = (Data_Read_in || Data_Write_in);

  // ------------------------------------------------------------
  // Reset behavior (checked even during reset)
  // ------------------------------------------------------------
  a_reset_state: assert property (@(posedge Clock_in)
      Reset_in |-> (Bus_Locked==2'b00 && Bus_Select==1'b0 &&
                    Inst_Ready_out==1'b0 && Data_Ready_out==1'b0 &&
                    Inst_Data_out==4096'd0 && Data_Data_out==4096'd0 &&
                    SD_Read_in==1'b0 && SD_Write_in==1'b0 &&
                    SD_Address_in==30'd0 && SD_Data_in==4096'd0));

  // ------------------------------------------------------------
  // State encoding and no-X basic sanity
  // ------------------------------------------------------------
  a_state_valid:  assert property (!$isunknown(Bus_Locked) && Bus_Locked!=2'b11);
  a_sel_no_x:     assert property (!$isunknown(Bus_Select));
  a_ready_mutex:  assert property (!(Inst_Ready_out && Data_Ready_out));

  // ------------------------------------------------------------
  // Bus_Locked next-state behavior (priority: Data over Inst on tie)
  // ------------------------------------------------------------
  // From idle (00)
  a_00_to_inst: assert property ((Bus_Locked==2'b00 && !SD_Ready_out &&  inst_act && !data_act) |=> Bus_Locked==2'b10);
  a_00_to_data: assert property ((Bus_Locked==2'b00 && !SD_Ready_out &&  data_act               ) |=> Bus_Locked==2'b01); // includes both-active
  a_00_hold:    assert property ((Bus_Locked==2'b00 && !( !SD_Ready_out && (inst_act||data_act) )) |=> Bus_Locked==2'b00);

  // From data-locked (01)
  a_01_to_inst: assert property ((Bus_Locked==2'b01 && !data_act && !SD_Ready_out &&  inst_act) |=> Bus_Locked==2'b10);
  a_01_to_idle: assert property ((Bus_Locked==2'b01 && !data_act && !SD_Ready_out && !inst_act) |=> Bus_Locked==2'b00);
  a_01_hold:    assert property ((Bus_Locked==2'b01 && (data_act || SD_Ready_out))              |=> Bus_Locked==2'b01);

  // From inst-locked (10)
  a_10_to_data: assert property ((Bus_Locked==2'b10 &&  data_act && !SD_Ready_out && !inst_act) |=> Bus_Locked==2'b01);
  a_10_to_idle: assert property ((Bus_Locked==2'b10 && !data_act && !SD_Ready_out && !inst_act) |=> Bus_Locked==2'b00);
  a_10_hold:    assert property ((Bus_Locked==2'b10 && (inst_act || SD_Ready_out))              |=> Bus_Locked==2'b10);

  // ------------------------------------------------------------
  // Bus_Select mapping to Bus_Locked and hold in idle
  // ------------------------------------------------------------
  a_sel_map_01:  assert property (Bus_Locked==2'b01 |-> Bus_Select==1'b1);
  a_sel_map_10:  assert property (Bus_Locked==2'b10 |-> Bus_Select==1'b0);
  a_sel_hold_00: assert property (Bus_Locked==2'b00 |=> Bus_Select==$past(Bus_Select));

  // ------------------------------------------------------------
  // Muxing correctness to SD side and READY propagation
  // ------------------------------------------------------------
  a_mux_inst: assert property ((!Bus_Select) |->
                  (SD_Read_in==Inst_Read_in &&
                   SD_Write_in==Inst_Write_in &&
                   SD_Address_in==Inst_Address_in &&
                   SD_Data_in==Inst_Data_in &&
                   Inst_Ready_out==SD_Ready_out &&
                   Data_Ready_out==1'b0));

  a_mux_data: assert property (( Bus_Select) |->
                  (SD_Read_in==Data_Read_in &&
                   SD_Write_in==Data_Write_in &&
                   SD_Address_in==Data_Address_in &&
                   SD_Data_in==Data_Data_in &&
                   Data_Ready_out==SD_Ready_out &&
                   Inst_Ready_out==1'b0));

  // Return data mirroring (both ports always mirror SD_Data_out when not in reset)
  a_data_out_eq: assert property (Inst_Data_out==SD_Data_out && Data_Data_out==SD_Data_out);

  // Key signals are not X when not in reset
  a_no_x_outputs: assert property (!$isunknown({Inst_Ready_out, Data_Ready_out,
                                               Inst_Data_out,  Data_Data_out,
                                               SD_Read_in, SD_Write_in, SD_Address_in, SD_Data_in}));

  // ------------------------------------------------------------
  // Functional coverage
  // ------------------------------------------------------------
  // Both-active tie goes to Data
  c_tie_data_wins: cover property (Bus_Locked==2'b00 && !SD_Ready_out && inst_act && data_act ##1 Bus_Locked==2'b01);

  // Grant each master from idle
  c_idle_to_inst:  cover property (Bus_Locked==2'b00 && !SD_Ready_out &&  inst_act && !data_act ##1 Bus_Locked==2'b10);
  c_idle_to_data:  cover property (Bus_Locked==2'b00 && !SD_Ready_out &&  data_act && !inst_act ##1 Bus_Locked==2'b01);

  // Switch between masters
  c_data_to_inst:  cover property (Bus_Locked==2'b01 && !data_act && !SD_Ready_out &&  inst_act ##1 Bus_Locked==2'b10);
  c_inst_to_data:  cover property (Bus_Locked==2'b10 &&  data_act && !SD_Ready_out && !inst_act ##1 Bus_Locked==2'b01);

  // Release to idle
  c_data_to_idle:  cover property (Bus_Locked==2'b01 && !data_act && !SD_Ready_out && !inst_act ##1 Bus_Locked==2'b00);
  c_inst_to_idle:  cover property (Bus_Locked==2'b10 && !data_act && !SD_Ready_out && !inst_act ##1 Bus_Locked==2'b00);

  // Observe READY propagation on both sides
  c_ready_inst:    cover property (!Bus_Select && SD_Ready_out && Inst_Ready_out && !Data_Ready_out);
  c_ready_data:    cover property ( Bus_Select && SD_Ready_out && Data_Ready_out && !Inst_Ready_out);

  // Observe Bus_Select toggling
  c_sel_toggle:    cover property (Bus_Select ##1 !Bus_Select ##1 Bus_Select);

endmodule

// Bind the SVA to all Bus_Arbiter instances
bind Bus_Arbiter Bus_Arbiter_sva sva();