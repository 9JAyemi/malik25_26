// SVA for FB_RejectArmController
// Bind this file to the DUT

module FB_RejectArmController_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        RejectCanister_eI,
  input  logic        LasersChanged_eI,
  input  logic        RejectSiteLaser_I,
  input  logic        GoRejectArm_eO,
  input  logic [1:0]  state,
  input  logic        RejectSiteLaser,
  input  logic        entered
);

  // State encodings (mirror DUT)
  localparam int S_Clear         = 2'd0;
  localparam int S_AwaitCanister = 2'd1;
  localparam int S_GoReject      = 2'd2;

  default clocking cb @(posedge clk); endclocking

  // past_valid guard for $past usage
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Reset behavior
  a_reset_vals: assert property (reset |-> state == S_Clear && !GoRejectArm_eO && (RejectSiteLaser == 1'b0));

  // No X on key regs/outputs
  a_no_x: assert property (disable iff (reset) !$isunknown({state, GoRejectArm_eO, RejectSiteLaser}));

  // State legality
  a_state_legal: assert property (disable iff (reset) state inside {S_Clear, S_AwaitCanister, S_GoReject});

  // entered flag matches state change
  a_enter_matches_change: assert property (disable iff (reset || !past_valid)
                                           entered == (state != $past(state)));

  // Latching of RejectSiteLaser
  a_laser_update: assert property (disable iff (reset) LasersChanged_eI |-> (RejectSiteLaser == RejectSiteLaser_I));
  a_laser_hold:   assert property (disable iff (reset || !past_valid) !LasersChanged_eI |-> (RejectSiteLaser == $past(RejectSiteLaser)));

  // Transition rules (prev-state/current-inputs -> current-state)
  // Clear
  a_clr_to_await: assert property (disable iff (reset || !past_valid)
                                   ($past(state) == S_Clear && RejectCanister_eI) |-> (state == S_AwaitCanister));
  a_clr_stay:     assert property (disable iff (reset || !past_valid)
                                   ($past(state) == S_Clear && !RejectCanister_eI) |-> (state == S_Clear));

  // AwaitCanister
  a_await_to_go:  assert property (disable iff (reset || !past_valid)
                                   ($past(state) == S_AwaitCanister && (LasersChanged_eI && RejectSiteLaser_I)) |-> (state == S_GoReject));
  a_await_stay:   assert property (disable iff (reset || !past_valid)
                                   ($past(state) == S_AwaitCanister && !(LasersChanged_eI && RejectSiteLaser_I)) |-> (state == S_AwaitCanister));

  // GoReject
  a_go_to_await:  assert property (disable iff (reset || !past_valid)
                                   ($past(state) == S_GoReject && RejectCanister_eI) |-> (state == S_AwaitCanister));
  a_go_stay:      assert property (disable iff (reset || !past_valid)
                                   ($past(state) == S_GoReject && !RejectCanister_eI) |-> (state == S_GoReject));

  // Output behavior:
  // Exact definition: pulse when entering GoReject from Await with (LasersChanged && RejectSiteLaser_I)
  a_go_def:       assert property (disable iff (reset || !past_valid)
                                   GoRejectArm_eO ==
                                   (($past(state) == S_AwaitCanister) && (LasersChanged_eI && RejectSiteLaser_I)));

  // Output asserted only while in GoReject entry cycle
  a_go_implies_state: assert property (disable iff (reset) GoRejectArm_eO |-> (state == S_GoReject));
  a_go_single_cycle:  assert property (disable iff (reset) GoRejectArm_eO |=> !GoRejectArm_eO);

  // Coverage
  c_clear_to_await:  cover property (disable iff (reset || !past_valid)
                                     ($past(state) == S_Clear && RejectCanister_eI) ##0 (state == S_AwaitCanister));
  c_await_to_go:     cover property (disable iff (reset || !past_valid)
                                     ($past(state) == S_AwaitCanister && (LasersChanged_eI && RejectSiteLaser_I)) ##0 (state == S_GoReject) and GoRejectArm_eO);
  c_go_to_await:     cover property (disable iff (reset || !past_valid)
                                     ($past(state) == S_GoReject && RejectCanister_eI) ##0 (state == S_AwaitCanister));
  c_full_loop:       cover property (disable iff (reset || !past_valid)
                                     ($past(state)==S_Clear && RejectCanister_eI) ##0 (state==S_AwaitCanister)
                                     ##1 (LasersChanged_eI && RejectSiteLaser_I) ##0 (state==S_GoReject && GoRejectArm_eO)
                                     ##1 RejectCanister_eI ##0 (state==S_AwaitCanister));

endmodule

bind FB_RejectArmController FB_RejectArmController_sva sva (
  .clk               (clk),
  .reset             (reset),
  .RejectCanister_eI (RejectCanister_eI),
  .LasersChanged_eI  (LasersChanged_eI),
  .RejectSiteLaser_I (RejectSiteLaser_I),
  .GoRejectArm_eO    (GoRejectArm_eO),
  .state             (state),
  .RejectSiteLaser   (RejectSiteLaser),
  .entered           (entered)
);