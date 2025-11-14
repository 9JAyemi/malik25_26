// SVA for SensorFSM
module SensorFSM_sva #(parameter DataWidth = 8) (
  input  logic                      Reset_n_i,
  input  logic                      Clk_i,
  input  logic                      Enable_i,
  input  logic                      MeasureFSM_Done_i,
  input  logic                      MeasureFSM_Error_i,
  input  logic [DataWidth-1:0]      MeasureFSM_Byte0_i,
  input  logic [DataWidth-1:0]      MeasureFSM_Byte1_i,
  input  logic [2*DataWidth-1:0]    ParamThreshold_i,
  input  logic [2*DataWidth-1:0]    ParamCounterPresetH_i,
  input  logic [2*DataWidth-1:0]    ParamCounterPresetL_i,
  input  logic                      CpuIntr_o,
  input  logic [2*DataWidth-1:0]    SensorValue_o,
  input  logic                      MeasureFSM_Start_o,
  // internal
  input  logic [2:0]                SensorFSM_State,
  input  logic                      SensorFSM_TimerOvfl,
  input  logic                      SensorFSM_TimerPreset,
  input  logic                      SensorFSM_TimerEnable,
  input  logic                      SensorFSM_DiffTooLarge,
  input  logic                      SensorFSM_StoreNewValue,
  input  logic [2*DataWidth-1:0]    SensorValue,
  input  logic [2*DataWidth-1:0]    Word0,
  input  logic [2*DataWidth-1:0]    AbsDiffResult,
  input  logic [31:0]               SensorFSM_Timer
);

  localparam stDisabled = 3'b000;
  localparam stIdle     = 3'b001;
  localparam stXfer     = 3'b010;
  localparam stNotify   = 3'b011;
  localparam stError    = 3'b100;

  default clocking cb @(posedge Clk_i); endclocking
  default disable iff (!Reset_n_i)

  // Async reset effects
  assert property (@(negedge Reset_n_i) SensorFSM_State==stDisabled && SensorFSM_Timer=='0 && Word0=='0);

  // State coding legal
  assert property (SensorFSM_State inside {stDisabled,stIdle,stXfer,stNotify,stError});

  // Timer control decode by state
  assert property ((SensorFSM_State==stIdle)    |-> (!SensorFSM_TimerPreset &&  SensorFSM_TimerEnable));
  assert property ((SensorFSM_State==stXfer)    |-> ( SensorFSM_TimerPreset && !SensorFSM_TimerEnable));
  assert property ((SensorFSM_State==stNotify)  |-> ( SensorFSM_TimerPreset && !SensorFSM_TimerEnable));
  assert property ((SensorFSM_State==stError)   |-> ( SensorFSM_TimerPreset && !SensorFSM_TimerEnable));
  assert property ((SensorFSM_State==stDisabled && !Enable_i) |-> ( SensorFSM_TimerPreset && !SensorFSM_TimerEnable));
  assert property ((SensorFSM_State==stDisabled &&  Enable_i) |-> (!SensorFSM_TimerPreset &&  SensorFSM_TimerEnable));

  // Start pulse only when Idle+Ovfl, and then go to Xfer
  assert property (MeasureFSM_Start_o |-> (SensorFSM_State==stIdle && Enable_i && SensorFSM_TimerOvfl));
  assert property ((SensorFSM_State==stIdle && Enable_i && SensorFSM_TimerOvfl) |-> MeasureFSM_Start_o ##1 SensorFSM_State==stXfer);

  // Interrupt gating
  assert property (CpuIntr_o |-> ((SensorFSM_State==stNotify) || (SensorFSM_State==stXfer && MeasureFSM_Error_i)));
  assert property ((SensorFSM_State==stXfer && MeasureFSM_Error_i) |-> CpuIntr_o ##1 SensorFSM_State==stError);
  assert property ((SensorFSM_State==stNotify) |-> CpuIntr_o ##1 SensorFSM_State==stIdle);

  // StoreNewValue gating and effect
  assert property (SensorFSM_StoreNewValue |-> (SensorFSM_State==stXfer && MeasureFSM_Done_i && SensorFSM_DiffTooLarge));
  assert property ((SensorFSM_State==stXfer && MeasureFSM_Done_i && SensorFSM_DiffTooLarge)
                   |-> SensorFSM_StoreNewValue ##1 SensorFSM_State==stNotify);
  assert property (SensorFSM_StoreNewValue |=> Word0 == {$past(MeasureFSM_Byte1_i), $past(MeasureFSM_Byte0_i)});
  assert property ((!SensorFSM_StoreNewValue) |=> Word0 == $past(Word0));
  assert property (SensorValue_o == Word0);

  // Xfer non-store paths
  assert property ((SensorFSM_State==stXfer && !MeasureFSM_Error_i && MeasureFSM_Done_i && !SensorFSM_DiffTooLarge)
                   |=> SensorFSM_State==stIdle && !SensorFSM_StoreNewValue && !CpuIntr_o);
  assert property ((SensorFSM_State==stXfer && !MeasureFSM_Error_i && !MeasureFSM_Done_i)
                   |=> SensorFSM_State==stXfer);

  // Disabled/Idle/Error transitions
  assert property ((SensorFSM_State==stDisabled && !Enable_i) |=> SensorFSM_State==stDisabled);
  assert property ((SensorFSM_State==stDisabled &&  Enable_i) |=> SensorFSM_State==stIdle);
  assert property ((SensorFSM_State==stIdle     && !Enable_i) |=> SensorFSM_State==stDisabled);
  assert property ((SensorFSM_State==stIdle     &&  Enable_i && !SensorFSM_TimerOvfl) |=> SensorFSM_State==stIdle);
  assert property ((SensorFSM_State==stError    &&  Enable_i) |=> SensorFSM_State==stError);
  assert property ((SensorFSM_State==stError    && !Enable_i) |=> SensorFSM_State==stDisabled);

  // Timer functional checks
  assert property (SensorFSM_TimerOvfl == (SensorFSM_Timer==32'd0));
  assert property (SensorFSM_TimerPreset |=> SensorFSM_Timer == {$past(ParamCounterPresetH_i), $past(ParamCounterPresetL_i)});
  assert property ((!SensorFSM_TimerPreset && SensorFSM_TimerEnable) |=> SensorFSM_Timer == $past(SensorFSM_Timer) - 1);

  // Absolute-diff and threshold logic
  logic [2*DataWidth:0] extA, extB;
  logic [2*DataWidth-1:0] refAbs;
  always_comb begin
    extA = {1'b0, {MeasureFSM_Byte1_i, MeasureFSM_Byte0_i}};
    extB = {1'b0, Word0};
    refAbs = (extA < extB) ? (extB[2*DataWidth-1:0] - extA[2*DataWidth-1:0])
                           : (extA[2*DataWidth-1:0] - extB[2*DataWidth-1:0]);
  end
  assert property (AbsDiffResult == refAbs);
  assert property (SensorFSM_DiffTooLarge == (AbsDiffResult > ParamThreshold_i));

  // Coverage
  cover property (SensorFSM_State==stIdle && Enable_i && SensorFSM_TimerOvfl ##0 MeasureFSM_Start_o
                  ##1 SensorFSM_State==stXfer ##[1:$] (MeasureFSM_Done_i && SensorFSM_DiffTooLarge)
                  ##1 SensorFSM_State==stNotify ##1 SensorFSM_State==stIdle);

  cover property (SensorFSM_State==stIdle && Enable_i && SensorFSM_TimerOvfl ##1 SensorFSM_State==stXfer
                  ##[1:$] (MeasureFSM_Error_i && CpuIntr_o) ##1 SensorFSM_State==stError
                  ##[1:$] (!Enable_i) ##1 SensorFSM_State==stDisabled);

  cover property (SensorFSM_State==stIdle && SensorFSM_TimerEnable && !SensorFSM_TimerPreset
                  ##1 SensorFSM_Timer == $past(SensorFSM_Timer)-1);

endmodule

// Bind into the DUT
bind SensorFSM SensorFSM_sva #(.DataWidth(DataWidth)) u_SensorFSM_sva (.*);