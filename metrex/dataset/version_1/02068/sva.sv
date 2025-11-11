// SVA for SensorFSM
module SensorFSM_sva #(parameter DataWidth = 8)
(
  input                       Reset_n_i,
  input                       Clk_i,
  input                       Enable_i,
  input                       CpuIntr_o,
  input      [2*DataWidth-1:0] SensorValueL_o,
  input      [2*DataWidth-1:0] SensorValueR_o,
  input                       MeasureFSM_QueryLocal_o,
  input                       MeasureFSM_QueryRemote_o,
  input                       MeasureFSM_Done_i,
  input                       MeasureFSM_Error_i,
  input      [DataWidth-1:0]  MeasureFSM_Byte0_i,
  input      [DataWidth-1:0]  MeasureFSM_Byte1_i,
  input      [2*DataWidth-1:0] ParamCounterPresetH_i,
  input      [2*DataWidth-1:0] ParamCounterPresetL_i,
  input       [2:0]           SensorFSM_State,
  input                       SensorFSM_TimerOvfl,
  input                       SensorFSM_TimerPreset,
  input                       SensorFSM_TimerEnable,
  input                       SensorFSM_StoreLocal,
  input                       SensorFSM_StoreRemote,
  input      [2*DataWidth-1:0] SensorValue,
  input      [2*DataWidth-1:0] WordL,
  input      [2*DataWidth-1:0] WordR,
  input       [31:0]          SensorFSM_Timer
);

  localparam stDisabled    = 3'd0;
  localparam stIdle        = 3'd1;
  localparam stQueryLocal  = 3'd2;
  localparam stWait1       = 3'd3;
  localparam stQueryRemote = 3'd4;
  localparam stNotify      = 3'd5;
  localparam stError       = 3'd6;

  default clocking cb @(posedge Clk_i); endclocking
  default disable iff (!Reset_n_i);

  // Basic sanity
  a_state_legal:        assert property (SensorFSM_State inside {stDisabled,stIdle,stQueryLocal,stWait1,stQueryRemote,stNotify,stError});
  a_reset_state:        assert property (!Reset_n_i |-> SensorFSM_State==stDisabled);
  a_reset_timer:        assert property (!Reset_n_i |-> SensorFSM_Timer==32'd0);
  a_reset_words:        assert property (!Reset_n_i |-> (WordL==0 && WordR==0));

  // Timer correctness
  a_ovfl_def:           assert property (SensorFSM_TimerOvfl == (SensorFSM_Timer==0));
  a_no_preset_enable:   assert property (!(SensorFSM_TimerPreset && SensorFSM_TimerEnable));
  a_preset_load:        assert property (SensorFSM_TimerPreset |=> SensorFSM_Timer == $past({ParamCounterPresetH_i,ParamCounterPresetL_i}));
  a_enable_dec:         assert property (!SensorFSM_TimerPreset && SensorFSM_TimerEnable |=> SensorFSM_Timer == $past(SensorFSM_Timer) - 1);
  a_hold_when_idle:     assert property (!SensorFSM_TimerPreset && !SensorFSM_TimerEnable |=> SensorFSM_Timer == $past(SensorFSM_Timer));

  // Idle timer gating and trigger to query
  a_idle_enable_cnt:    assert property (SensorFSM_State==stIdle && Enable_i && !SensorFSM_TimerOvfl |-> SensorFSM_TimerEnable);
  a_idle_no_cnt_on_ovf: assert property (SensorFSM_State==stIdle && SensorFSM_TimerOvfl |-> !SensorFSM_TimerEnable);
  a_idle_ovf_to_ql:     assert property (SensorFSM_State==stIdle && SensorFSM_TimerOvfl |-> MeasureFSM_QueryLocal_o && ##1 SensorFSM_State==stQueryLocal);

  // Disabled <-> Idle
  a_dis_to_idle:        assert property (SensorFSM_State==stDisabled && Enable_i |=> SensorFSM_State==stIdle && $past(SensorFSM_TimerPreset) && !$past(SensorFSM_TimerEnable));
  a_idle_to_dis:        assert property (SensorFSM_State==stIdle && !Enable_i |=> SensorFSM_State==stDisabled);

  // Query pulses
  a_ql_only_when_exp:   assert property (MeasureFSM_QueryLocal_o |-> (SensorFSM_State==stIdle && SensorFSM_TimerOvfl));
  a_ql_one_cycle:       assert property (MeasureFSM_QueryLocal_o |=> !MeasureFSM_QueryLocal_o);
  a_wait1_beh:          assert property (SensorFSM_State==stWait1 |-> MeasureFSM_QueryRemote_o && ##1 SensorFSM_State==stQueryRemote);
  a_qr_only_in_wait1:   assert property (MeasureFSM_QueryRemote_o |-> SensorFSM_State==stWait1);
  a_qr_one_cycle:       assert property (MeasureFSM_QueryRemote_o |=> !MeasureFSM_QueryRemote_o);

  // Handshake and store
  a_ql_done_store:      assert property (SensorFSM_State==stQueryLocal  && MeasureFSM_Done_i |-> SensorFSM_StoreLocal  && ##1 SensorFSM_State==stWait1);
  a_qr_done_store:      assert property (SensorFSM_State==stQueryRemote && MeasureFSM_Done_i |-> SensorFSM_StoreRemote && ##1 SensorFSM_State==stNotify);
  a_ql_err_to_err:      assert property (SensorFSM_State==stQueryLocal  && MeasureFSM_Error_i |-> CpuIntr_o && ##1 SensorFSM_State==stError);
  a_qr_err_to_err:      assert property (SensorFSM_State==stQueryRemote && MeasureFSM_Error_i |-> CpuIntr_o && ##1 SensorFSM_State==stError);

  // Notify behavior
  a_notify:             assert property (SensorFSM_State==stNotify |-> SensorFSM_TimerPreset && CpuIntr_o && ##1 SensorFSM_State==stIdle);

  // Error handling
  a_err_hold:           assert property (SensorFSM_State==stError && Enable_i  |=> SensorFSM_State==stError);
  a_err_to_dis:         assert property (SensorFSM_State==stError && !Enable_i |=> SensorFSM_State==stDisabled);

  // Interrupt exact conditions
  a_intr_only_where:    assert property (CpuIntr_o |-> (SensorFSM_State==stNotify) ||
                                                     (SensorFSM_State==stQueryLocal  && MeasureFSM_Error_i) ||
                                                     (SensorFSM_State==stQueryRemote && MeasureFSM_Error_i));
  a_intr_notify_req:    assert property (SensorFSM_State==stNotify |-> CpuIntr_o);
  a_intr_err_req_ql:    assert property (SensorFSM_State==stQueryLocal  && MeasureFSM_Error_i |-> CpuIntr_o);
  a_intr_err_req_qr:    assert property (SensorFSM_State==stQueryRemote && MeasureFSM_Error_i |-> CpuIntr_o);

  // Data path
  a_sensorvalue_concat: assert property (SensorValue == {MeasureFSM_Byte1_i,MeasureFSM_Byte0_i});
  a_wordl_update:       assert property ($past(SensorFSM_StoreLocal)  |-> WordL == $past(SensorValue));
  a_wordl_hold:         assert property (!SensorFSM_StoreLocal  |=> WordL == $past(WordL));
  a_wordr_update:       assert property ($past(SensorFSM_StoreRemote) |-> WordR == $past(SensorValue));
  a_wordr_hold:         assert property (!SensorFSM_StoreRemote |=> WordR == $past(WordR));
  a_out_match_regs:     assert property (SensorValueL_o==WordL && SensorValueR_o==WordR);

  // Coverage
  c_normal_flow: cover property (
      SensorFSM_State==stIdle && SensorFSM_TimerOvfl ##1
      SensorFSM_State==stQueryLocal && MeasureFSM_Done_i ##1
      SensorFSM_State==stWait1 ##1
      SensorFSM_State==stQueryRemote && MeasureFSM_Done_i ##1
      SensorFSM_State==stNotify ##1
      SensorFSM_State==stIdle
  );

  c_error_flow_from_ql: cover property (
      SensorFSM_State==stIdle && SensorFSM_TimerOvfl ##1
      SensorFSM_State==stQueryLocal && MeasureFSM_Error_i ##1
      SensorFSM_State==stError
  );

endmodule

bind SensorFSM SensorFSM_sva #(.DataWidth(DataWidth)) i_SensorFSM_sva (
  .Reset_n_i               (Reset_n_i),
  .Clk_i                   (Clk_i),
  .Enable_i                (Enable_i),
  .CpuIntr_o               (CpuIntr_o),
  .SensorValueL_o          (SensorValueL_o),
  .SensorValueR_o          (SensorValueR_o),
  .MeasureFSM_QueryLocal_o (MeasureFSM_QueryLocal_o),
  .MeasureFSM_QueryRemote_o(MeasureFSM_QueryRemote_o),
  .MeasureFSM_Done_i       (MeasureFSM_Done_i),
  .MeasureFSM_Error_i      (MeasureFSM_Error_i),
  .MeasureFSM_Byte0_i      (MeasureFSM_Byte0_i),
  .MeasureFSM_Byte1_i      (MeasureFSM_Byte1_i),
  .ParamCounterPresetH_i   (ParamCounterPresetH_i),
  .ParamCounterPresetL_i   (ParamCounterPresetL_i),
  .SensorFSM_State         (SensorFSM_State),
  .SensorFSM_TimerOvfl     (SensorFSM_TimerOvfl),
  .SensorFSM_TimerPreset   (SensorFSM_TimerPreset),
  .SensorFSM_TimerEnable   (SensorFSM_TimerEnable),
  .SensorFSM_StoreLocal    (SensorFSM_StoreLocal),
  .SensorFSM_StoreRemote   (SensorFSM_StoreRemote),
  .SensorValue             (SensorValue),
  .WordL                   (WordL),
  .WordR                   (WordR),
  .SensorFSM_Timer         (SensorFSM_Timer)
);