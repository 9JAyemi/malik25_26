// SVA for NPM_Toggle_POR
// Bindable checker that uses internal DUT signals for high-quality verification

module NPM_Toggle_POR_sva
#(
  parameter POR_FSM_BIT = 4,
  parameter [POR_FSM_BIT-1:0] POR_RESET = 4'b0001,
  parameter [POR_FSM_BIT-1:0] POR_READY = 4'b0010,
  parameter [POR_FSM_BIT-1:0] POR_RFRST = 4'b0100,
  parameter [POR_FSM_BIT-1:0] POR_RLOOP = 4'b1000
)(
  input  logic                          clk,
  input  logic                          rst,

  // DUT internals
  input  logic [POR_FSM_BIT-1:0]        rPOR_cur_state,
  input  logic [POR_FSM_BIT-1:0]        rPOR_nxt_state,
  input  logic                          rReady,
  input  logic [3:0]                    rTimer,
  input  logic                          rPO_Reset,
  input  logic                          iStart,
  input  logic                          wJOBDone,

  // DUT outputs
  input  logic                          oReady,
  input  logic                          oLastStep,
  input  logic                          oPO_Reset
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Basic sanity
  a_state_legal:     assert property ($onehot(rPOR_cur_state) &&
                                      rPOR_cur_state inside {POR_RESET, POR_READY, POR_RFRST, POR_RLOOP});
  a_state_update:    assert property (rPOR_cur_state == $past(rPOR_nxt_state));

  // Next-state function correctness
  a_ns_reset:        assert property (rPOR_cur_state == POR_RESET |-> rPOR_nxt_state == POR_READY);
  a_ns_ready_hold:   assert property (rPOR_cur_state == POR_READY && !iStart |-> rPOR_nxt_state == POR_READY);
  a_ns_ready_start:  assert property (rPOR_cur_state == POR_READY &&  iStart |-> rPOR_nxt_state == POR_RFRST);
  a_ns_rfrst:        assert property (rPOR_cur_state == POR_RFRST |-> rPOR_nxt_state == POR_RLOOP);
  a_ns_rloop_hold:   assert property (rPOR_cur_state == POR_RLOOP && !wJOBDone |-> rPOR_nxt_state == POR_RLOOP);
  a_ns_rloop_done0:  assert property (rPOR_cur_state == POR_RLOOP &&  wJOBDone && !iStart |-> rPOR_nxt_state == POR_READY);
  a_ns_rloop_done1:  assert property (rPOR_cur_state == POR_RLOOP &&  wJOBDone &&  iStart |-> rPOR_nxt_state == POR_RFRST);

  // Output decode vs next-state (sequential block uses rPOR_nxt_state)
  a_dec_ready:       assert property (rReady    == (rPOR_nxt_state == POR_READY));
  a_dec_reset:       assert property (rPO_Reset == (rPOR_nxt_state inside {POR_RFRST, POR_RLOOP}));
  a_dec_timer_rl:    assert property (rPOR_nxt_state == POR_RLOOP |-> rTimer == $past(rTimer) + 1'b1);
  a_dec_timer_nonrl: assert property (rPOR_nxt_state != POR_RLOOP |-> rTimer == 4'd0);

  // Derived signals and outputs must match RTL assigns
  a_wjob_eq:         assert property (wJOBDone <-> (rTimer == 4'd9));
  a_wjob_pulse:      assert property (wJOBDone |=> !wJOBDone); // one-cycle pulse
  a_oports_cons:     assert property (oLastStep == wJOBDone &&
                                      oPO_Reset == rPO_Reset &&
                                      oReady    == (rReady || wJOBDone));
  a_wjob_implies_ready: assert property (wJOBDone |-> oReady);

  // Functional intent: starting causes immediate reset assertion and timer clear
  a_ready_start_effect: assert property (rPOR_cur_state == POR_READY && iStart |->
                                         rPOR_nxt_state == POR_RFRST && rPO_Reset && !rReady && rTimer == 4'd0);

  // Progress: loop completes within 10 cycles (timer reaches 9)
  a_rloop_completes_10: assert property (rPOR_nxt_state == POR_RLOOP |-> ##[1:10] wJOBDone);

  // Asynchronous reset results (checked at clock): when rst is high at a posedge, state/output regs must be reset
  a_async_reset_effect: assert property ($rose(rst) or rst |-> (rPOR_cur_state == POR_RESET))
    else $error("State not POR_RESET while reset asserted");

  // No X on primary outputs
  a_no_x: assert property (!$isunknown({oReady, oLastStep, oPO_Reset}));

  // Coverage
  c_reset_to_ready:  cover property ($fell(rst) ##1 rPOR_cur_state == POR_RESET ##1 rPOR_nxt_state == POR_READY && oReady);
  c_ready_to_rfrst:  cover property (rPOR_cur_state == POR_READY && iStart ##1 rPOR_nxt_state == POR_RFRST);
  c_rfrst_to_rloop:  cover property (rPOR_cur_state == POR_RFRST ##1 rPOR_nxt_state == POR_RLOOP);
  c_rloop_hold:      cover property (rPOR_cur_state == POR_RLOOP && !wJOBDone [*3]);
  c_done_to_ready:   cover property (rPOR_cur_state == POR_RLOOP && wJOBDone && !iStart ##1 rPOR_nxt_state == POR_READY && oReady && oLastStep);
  c_done_to_rfrst:   cover property (rPOR_cur_state == POR_RLOOP && wJOBDone &&  iStart ##1 rPOR_nxt_state == POR_RFRST && oReady && oLastStep);
  c_two_loops:       cover property (rPOR_cur_state == POR_READY && iStart ##1
                                     rPOR_cur_state == POR_RFRST ##1
                                     (rPOR_cur_state == POR_RLOOP && !wJOBDone)[*8] ##1
                                     rPOR_cur_state == POR_RLOOP && wJOBDone && iStart ##1
                                     rPOR_cur_state == POR_RFRST);

endmodule

// Bind into DUT (connect internal signals)
bind NPM_Toggle_POR NPM_Toggle_POR_sva
#(
  .POR_FSM_BIT(POR_FSM_BIT),
  .POR_RESET  (POR_RESET),
  .POR_READY  (POR_READY),
  .POR_RFRST  (POR_RFRST),
  .POR_RLOOP  (POR_RLOOP)
) NPM_Toggle_POR_sva_i (
  .clk            (iSystemClock),
  .rst            (iReset),

  .rPOR_cur_state (rPOR_cur_state),
  .rPOR_nxt_state (rPOR_nxt_state),
  .rReady         (rReady),
  .rTimer         (rTimer),
  .rPO_Reset      (rPO_Reset),
  .iStart         (iStart),
  .wJOBDone       (wJOBDone),

  .oReady         (oReady),
  .oLastStep      (oLastStep),
  .oPO_Reset      (oPO_Reset)
);