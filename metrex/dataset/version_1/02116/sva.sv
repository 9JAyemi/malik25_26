// SVA for FB_IOManager — concise, high-coverage checks
// Bind this checker to the DUT
module FB_IOManager_sva;

  // local view of DUT constants
  localparam int STATE_Start = 0;

  // Default SVA context
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset default values one cycle after a rising reset
  a_reset_defaults:
    assert property (disable iff (1'b0)
      $rose(reset) |-> ##1 (
        state == STATE_Start
        && !InjectorArmFinishMovement && !EmergencyStopChanged && !CanisterPressureChanged
        && !FillContentsAvailableChanged && !LasersChanged && !DoorOverride && !VacuumTimerElapsed
        && ConveyorSpeed == 8'd0 && InjectorPosition == 8'd0
        && !InjectorContentsValveOpen && !InjectorVacuumRun && !InjectorPressurePumpRun
        && !FillContents && CanisterCount == 8'd0
        && !EmergencyStop && CanisterPressure == 8'd0 && FillContentsAvailable == 8'd0
        && !DoorSiteLaser && !InjectSiteLaser && !RejectSiteLaser && !RejectBinLaser && !AcceptBinLaser
        && !EmergencyStopped
      ));

  // FSM stays in Start
  a_state_stuck: assert property (state == STATE_Start);

  // entered <-> IOAlgorithm enable equivalence and behavior in Start
  a_alg_en_match:       assert property (IOAlgorithm_alg_en == entered);
  a_alg_en_when_start:  assert property ((entered && state==STATE_Start) |-> ##0 IOAlgorithm_alg_en);

  // EmergencyStopChanged asserted whenever we "enter" Start
  a_emerg_chg_on_enter: assert property ((entered && state==STATE_Start) |-> ##0 EmergencyStopChanged);

  // Input-change driven latching
  a_latch_conveyor: assert property (ConveyorChanged |-> ##0 (ConveyorSpeed == ConveyorSpeed_I));
  a_hold_conveyor:  assert property (!ConveyorChanged |-> $stable(ConveyorSpeed));

  a_latch_injpos:   assert property (InjectorPositionChanged |-> ##0 (InjectorPosition == InjectorPosition_I));
  a_hold_injpos:    assert property (!InjectorPositionChanged |-> $stable(InjectorPosition));

  a_latch_ctrls:    assert property (InjectorControlsChanged |-> ##0 (
                          InjectorContentsValveOpen == InjectorContentsValveOpen_I
                       && InjectorVacuumRun         == InjectorVacuumRun_I
                       && InjectorPressurePumpRun   == InjectorPressurePumpRun_I));
  a_hold_ctrls:     assert property (!InjectorControlsChanged |-> (
                          $stable(InjectorContentsValveOpen)
                       && $stable(InjectorVacuumRun)
                       && $stable(InjectorPressurePumpRun)));

  a_latch_fill:     assert property (FillContentsChanged |-> ##0 (FillContents == FillContents_I));
  a_hold_fill:      assert property (!FillContentsChanged |-> $stable(FillContents));

  a_latch_count:    assert property (CanisterCountChanged |-> ##0 (CanisterCount == CanisterCount_I));
  a_hold_count:     assert property (!CanisterCountChanged |-> $stable(CanisterCount));

  // eO mirrors (sanity)
  a_mirror_iam:       assert property (InjectorArmFinishMovement_eO == InjectorArmFinishMovement);
  a_mirror_emergchg:  assert property (EmergencyStopChanged_eO == EmergencyStopChanged);
  a_mirror_presschg:  assert property (CanisterPressureChanged_eO == CanisterPressureChanged);
  a_mirror_fillchg:   assert property (FillContentsAvailableChanged_eO == FillContentsAvailableChanged);
  a_mirror_laschg:    assert property (LasersChanged_eO == LasersChanged);
  a_mirror_doorovr:   assert property (DoorOverride_eO == DoorOverride);
  a_mirror_vactmr:    assert property (VacuumTimerElapsed_eO == VacuumTimerElapsed);

  // Output update gating by corresponding *_Changed and value match on change
  a_gate_emerg_out:       assert property ($changed(EmergencyStop_O) |-> EmergencyStopChanged);
  a_emerg_match_on_chg:   assert property (EmergencyStopChanged |-> ##0 (EmergencyStop_O == EmergencyStop));

  a_gate_press_out:       assert property ($changed(CanisterPressure_O) |-> CanisterPressureChanged);
  a_press_match_on_chg:   assert property (CanisterPressureChanged |-> ##0 (CanisterPressure_O == CanisterPressure));

  a_gate_fill_out:        assert property ($changed(FillContentsAvailable_O) |-> FillContentsAvailableChanged);
  a_fill_match_on_chg:    assert property (FillContentsAvailableChanged |-> ##0 (FillContentsAvailable_O == FillContentsAvailable));

  a_gate_lasers_out:      assert property (
                             ($changed(DoorSiteLaser_O) || $changed(InjectSiteLaser_O) ||
                              $changed(RejectSiteLaser_O) || $changed(RejectBinLaser_O) ||
                              $changed(AcceptBinLaser_O)) |-> LasersChanged);
  a_lasers_match_on_chg:  assert property (LasersChanged |-> ##0 (
                             DoorSiteLaser_O   == DoorSiteLaser   &&
                             InjectSiteLaser_O == InjectSiteLaser &&
                             RejectSiteLaser_O == RejectSiteLaser &&
                             RejectBinLaser_O  == RejectBinLaser  &&
                             AcceptBinLaser_O  == AcceptBinLaser));

  // No X/Z after reset on key latched/internal regs
  a_no_x_internal: assert property (
    !$isunknown({ConveyorSpeed, InjectorPosition,
                 InjectorContentsValveOpen, InjectorVacuumRun, InjectorPressurePumpRun,
                 FillContents, CanisterCount,
                 EmergencyStop, CanisterPressure, FillContentsAvailable,
                 DoorSiteLaser, InjectSiteLaser, RejectSiteLaser, RejectBinLaser, AcceptBinLaser}));

  // Coverage: observe each path at least once
  c_conveyor: cover property (ConveyorChanged ##1 (ConveyorSpeed == ConveyorSpeed_I));
  c_injpos:   cover property (InjectorPositionChanged ##1 (InjectorPosition == InjectorPosition_I));
  c_ctrls:    cover property (InjectorControlsChanged ##1 (
                    InjectorContentsValveOpen == InjectorContentsValveOpen_I &&
                    InjectorVacuumRun         == InjectorVacuumRun_I &&
                    InjectorPressurePumpRun   == InjectorPressurePumpRun_I));
  c_fill:     cover property (FillContentsChanged ##1 (FillContents == FillContents_I));
  c_count:    cover property (CanisterCountChanged ##1 (CanisterCount == CanisterCount_I));
  c_lasers:   cover property (LasersChanged ##1 (
                    DoorSiteLaser_O   == DoorSiteLaser   &&
                    InjectSiteLaser_O == InjectSiteLaser &&
                    RejectSiteLaser_O == RejectSiteLaser &&
                    RejectBinLaser_O  == RejectBinLaser  &&
                    AcceptBinLaser_O  == AcceptBinLaser));
  c_alg_en:   cover property (IOAlgorithm_alg_en);

endmodule

bind FB_IOManager FB_IOManager_sva;