// SVA checker for manufacturing_process_controller
module mfg_ctrl_sva(
  input logic clk,
  input logic reset,

  // input events
  input logic InjectorArmFinishMovement_eI,
  input logic EmergencyStopChanged_eI,
  input logic CanisterPressureChanged_eI,
  input logic FillContentsAvailableChanged_eI,
  input logic LasersChanged_eI,
  input logic DoorOverride_eI,
  input logic VacuumTimerElapsed_eI,

  // output events
  input logic DoorReleaseCanister_eO,
  input logic ConveyorChanged_eO,
  input logic InjectorPositionChanged_eO,
  input logic InjectorControlsChanged_eO,
  input logic FillContentsChanged_eO,
  input logic StartVacuumTimer_eO,
  input logic GoRejectArm_eO,
  input logic CanisterCountChanged_eO,
  input logic InjectDone_eO,

  // input variables
  input logic EmergencyStop_I,
  input logic [7:0] CanisterPressure_I,
  input logic [7:0] FillContentsAvailable_I,
  input logic DoorSiteLaser_I,
  input logic InjectSiteLaser_I,
  input logic RejectSiteLaser_I,
  input logic RejectBinLaser_I,
  input logic AcceptBinLaser_I,

  // output variables
  input logic [7:0] ConveyorSpeed_O,
  input logic [7:0] InjectorPosition_O,
  input logic InjectorContentsValveOpen_O,
  input logic InjectorVacuumRun_O,
  input logic InjectorPressurePumpRun_O,
  input logic [7:0] FillContents_O,
  input logic [7:0] CanisterCount_O
);

  // Reset behavior: immediately and after assertion
  // Hold zeros while reset is high
  assert property (@(posedge clk)
    reset |-> (ConveyorSpeed_O==0 && InjectorPosition_O==0 &&
               !InjectorContentsValveOpen_O && !InjectorVacuumRun_O && !InjectorPressurePumpRun_O &&
               FillContents_O==0 && CanisterCount_O==0 &&
               !InjectDone_eO && !DoorReleaseCanister_eO && !ConveyorChanged_eO &&
               !InjectorPositionChanged_eO && !InjectorControlsChanged_eO &&
               !FillContentsChanged_eO && !StartVacuumTimer_eO &&
               !GoRejectArm_eO && !CanisterCountChanged_eO));

  // On reset assertion, next cycle all outputs are cleared
  assert property (@(posedge clk)
    $rose(reset) |=> (ConveyorSpeed_O==0 && InjectorPosition_O==0 &&
                      !InjectorContentsValveOpen_O && !InjectorVacuumRun_O && !InjectorPressurePumpRun_O &&
                      FillContents_O==0 && CanisterCount_O==0 &&
                      !InjectDone_eO && !DoorReleaseCanister_eO && !ConveyorChanged_eO &&
                      !InjectorPositionChanged_eO && !InjectorControlsChanged_eO &&
                      !FillContentsChanged_eO && !StartVacuumTimer_eO &&
                      !GoRejectArm_eO && !CanisterCountChanged_eO));

  // All outputs known (no X/Z)
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown({ConveyorSpeed_O, InjectorPosition_O, InjectorContentsValveOpen_O,
                 InjectorVacuumRun_O, InjectorPressurePumpRun_O, FillContents_O, CanisterCount_O,
                 InjectDone_eO, DoorReleaseCanister_eO, ConveyorChanged_eO,
                 InjectorPositionChanged_eO, InjectorControlsChanged_eO,
                 FillContentsChanged_eO, StartVacuumTimer_eO, GoRejectArm_eO, CanisterCountChanged_eO}));

  // Emergency stop forces key controls off
  assert property (@(posedge clk) disable iff (reset)
    (EmergencyStopChanged_eI && EmergencyStop_I)
      |=> (ConveyorSpeed_O==8'd0 && !InjectorVacuumRun_O && !InjectorPressurePumpRun_O));

  // Canister pressure > 200 increments conveyor and sets changed flag
  assert property (@(posedge clk) disable iff (reset)
    (CanisterPressureChanged_eI && (CanisterPressure_I > 8'd200))
      |=> (ConveyorSpeed_O == $past(ConveyorSpeed_O + 8'd1)) && ConveyorChanged_eO);

  // Fill contents update and flag
  assert property (@(posedge clk) disable iff (reset)
    FillContentsAvailableChanged_eI
      |=> (FillContents_O == $past(FillContentsAvailable_I)) && FillContentsChanged_eO);

  // Lasers: door release when door and reject sites are occupied
  assert property (@(posedge clk) disable iff (reset)
    (LasersChanged_eI && DoorSiteLaser_I && RejectSiteLaser_I)
      |=> DoorReleaseCanister_eO);

  // Lasers: injector position set and flag
  assert property (@(posedge clk) disable iff (reset)
    (LasersChanged_eI && InjectSiteLaser_I)
      |=> (InjectorPosition_O == 8'hFF) && InjectorPositionChanged_eO);

  // Lasers: reject bin command
  assert property (@(posedge clk) disable iff (reset)
    (LasersChanged_eI && RejectBinLaser_I)
      |=> GoRejectArm_eO);

  // Lasers: accept bin increments count and sets flag
  assert property (@(posedge clk) disable iff (reset)
    (LasersChanged_eI && AcceptBinLaser_I)
      |=> (CanisterCount_O == $past(CanisterCount_O + 8'd1)) && CanisterCountChanged_eO);

  // Vacuum timer elapsed shuts off vacuum path, marks done, and flags controls changed
  assert property (@(posedge clk) disable iff (reset)
    VacuumTimerElapsed_eI
      |=> (!StartVacuumTimer_eO && !InjectorContentsValveOpen_O && !InjectorVacuumRun_O &&
           InjectDone_eO && InjectorControlsChanged_eO));

  // Injector arm finish: start vacuum path and flag controls changed
  assert property (@(posedge clk) disable iff (reset)
    InjectorArmFinishMovement_eI
      |=> (StartVacuumTimer_eO && InjectorContentsValveOpen_O &&
           InjectorVacuumRun_O && InjectorPressurePumpRun_O && InjectorControlsChanged_eO));

  // Door override releases canister
  assert property (@(posedge clk) disable iff (reset)
    DoorOverride_eI |=> DoorReleaseCanister_eO);

  // Deterministic precedence when VacuumTimerElapsed and ArmFinish occur together
  // (later assignments in source win for valve/vacuum/start; inject_done remains set)
  assert property (@(posedge clk) disable iff (reset)
    (VacuumTimerElapsed_eI && InjectorArmFinishMovement_eI)
      |=> (StartVacuumTimer_eO && InjectorContentsValveOpen_O && InjectorVacuumRun_O &&
           InjectDone_eO && InjectorControlsChanged_eO));

  // Coverage

  cover property (@(posedge clk) disable iff (reset)
    (EmergencyStopChanged_eI && EmergencyStop_I) ##1
      (!InjectorVacuumRun_O && !InjectorPressurePumpRun_O && (ConveyorSpeed_O==8'd0)));

  cover property (@(posedge clk) disable iff (reset)
    (CanisterPressureChanged_eI && (CanisterPressure_I>8'd200)) ##1 ConveyorChanged_eO);

  cover property (@(posedge clk) disable iff (reset)
    FillContentsAvailableChanged_eI ##1 (FillContentsChanged_eO && (FillContents_O==$past(FillContentsAvailable_I))));

  cover property (@(posedge clk) disable iff (reset)
    (LasersChanged_eI && DoorSiteLaser_I && RejectSiteLaser_I) ##1 DoorReleaseCanister_eO);

  cover property (@(posedge clk) disable iff (reset)
    (LasersChanged_eI && InjectSiteLaser_I) ##1 (InjectorPositionChanged_eO && (InjectorPosition_O==8'hFF)));

  cover property (@(posedge clk) disable iff (reset)
    (LasersChanged_eI && AcceptBinLaser_I) ##1 (CanisterCountChanged_eO));

  cover property (@(posedge clk) disable iff (reset)
    (LasersChanged_eI && RejectBinLaser_I) ##1 GoRejectArm_eO);

  // End-to-end inject cycle: arm finishes -> start timer -> timer elapses -> inject done
  sequence s_inject_flow;
    InjectorArmFinishMovement_eI ##1 StartVacuumTimer_eO ##[1:20] VacuumTimerElapsed_eI ##1 InjectDone_eO;
  endsequence
  cover property (@(posedge clk) disable iff (reset) s_inject_flow);

endmodule

// Bind to DUT
bind manufacturing_process_controller mfg_ctrl_sva sva_inst(
  .clk(clk),
  .reset(reset),

  .InjectorArmFinishMovement_eI(InjectorArmFinishMovement_eI),
  .EmergencyStopChanged_eI(EmergencyStopChanged_eI),
  .CanisterPressureChanged_eI(CanisterPressureChanged_eI),
  .FillContentsAvailableChanged_eI(FillContentsAvailableChanged_eI),
  .LasersChanged_eI(LasersChanged_eI),
  .DoorOverride_eI(DoorOverride_eI),
  .VacuumTimerElapsed_eI(VacuumTimerElapsed_eI),

  .DoorReleaseCanister_eO(DoorReleaseCanister_eO),
  .ConveyorChanged_eO(ConveyorChanged_eO),
  .InjectorPositionChanged_eO(InjectorPositionChanged_eO),
  .InjectorControlsChanged_eO(InjectorControlsChanged_eO),
  .FillContentsChanged_eO(FillContentsChanged_eO),
  .StartVacuumTimer_eO(StartVacuumTimer_eO),
  .GoRejectArm_eO(GoRejectArm_eO),
  .CanisterCountChanged_eO(CanisterCountChanged_eO),
  .InjectDone_eO(InjectDone_eO),

  .EmergencyStop_I(EmergencyStop_I),
  .CanisterPressure_I(CanisterPressure_I),
  .FillContentsAvailable_I(FillContentsAvailable_I),
  .DoorSiteLaser_I(DoorSiteLaser_I),
  .InjectSiteLaser_I(InjectSiteLaser_I),
  .RejectSiteLaser_I(RejectSiteLaser_I),
  .RejectBinLaser_I(RejectBinLaser_I),
  .AcceptBinLaser_I(AcceptBinLaser_I),

  .ConveyorSpeed_O(ConveyorSpeed_O),
  .InjectorPosition_O(InjectorPosition_O),
  .InjectorContentsValveOpen_O(InjectorContentsValveOpen_O),
  .InjectorVacuumRun_O(InjectorVacuumRun_O),
  .InjectorPressurePumpRun_O(InjectorPressurePumpRun_O),
  .FillContents_O(FillContents_O),
  .CanisterCount_O(CanisterCount_O)
);