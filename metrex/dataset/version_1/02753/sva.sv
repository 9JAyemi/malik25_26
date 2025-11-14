// SVA for axi_protocol_converter_v2_1_8_b2s_wr_cmd_fsm
module axi_protocol_converter_v2_1_8_b2s_wr_cmd_fsm_sva
(
  input  logic        clk,
  input  logic        reset,
  input  logic        s_awvalid,
  input  logic        m_awready,
  input  logic        next_pending,
  input  logic        b_full,
  output logic        s_awready,
  output logic        m_awvalid,
  output logic        next,
  output logic        b_push,
  output logic        a_push,
  input  logic [1:0]  state,
  input  logic [1:0]  next_state
);

  localparam logic [1:0] SM_IDLE         = 2'b00;
  localparam logic [1:0] SM_CMD_EN       = 2'b01;
  localparam logic [1:0] SM_CMD_ACCEPTED = 2'b10;
  localparam logic [1:0] SM_DONE_WAIT    = 2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Reset and basic FSM well-formedness
  ap_reset_to_idle:      assert property (reset |=> state == SM_IDLE);
  ap_state_known:        assert property (!reset |-> (state inside {SM_IDLE,SM_CMD_EN,SM_CMD_ACCEPTED,SM_DONE_WAIT}));
  ap_state_updates_from_next: assert property (!reset |=> state == $past(next_state));

  // FSM next-state behavior
  ap_idle_hold:          assert property ((state==SM_IDLE && !s_awvalid) |=> state==SM_IDLE);
  ap_idle_to_cmd_en:     assert property ((state==SM_IDLE &&  s_awvalid) |=> state==SM_CMD_EN);

  ap_cmd_en_to_acc:      assert property ((state==SM_CMD_EN && m_awready &&  next_pending                 ) |=> state==SM_CMD_ACCEPTED);
  ap_cmd_en_to_done:     assert property ((state==SM_CMD_EN && m_awready && !next_pending &&  b_full      ) |=> state==SM_DONE_WAIT);
  ap_cmd_en_to_idle:     assert property ((state==SM_CMD_EN && m_awready && !next_pending && !b_full      ) |=> state==SM_IDLE);
  ap_cmd_en_hold:        assert property ((state==SM_CMD_EN && !m_awready                                 ) |=> state==SM_CMD_EN);

  ap_acc_to_cmd_en:      assert property ( state==SM_CMD_ACCEPTED |=> state==SM_CMD_EN);

  ap_done_to_idle:       assert property ((state==SM_DONE_WAIT && !b_full) |=> state==SM_IDLE);
  ap_done_hold:          assert property ((state==SM_DONE_WAIT &&  b_full) |=> state==SM_DONE_WAIT);

  // Output correctness
  ap_m_awvalid_eq:       assert property (m_awvalid == (state==SM_CMD_EN));
  ap_a_push_eq:          assert property (a_push    == (state==SM_IDLE));

  ap_s_awready_eq:       assert property (s_awready ==
                                         ((state==SM_CMD_EN    && m_awready && !next_pending && !b_full) ||
                                          (state==SM_DONE_WAIT && !b_full)));

  ap_b_push_eq:          assert property (b_push == s_awready);

  ap_next_eq:            assert property (next == ((state==SM_CMD_ACCEPTED) || s_awready));

  // Single-cycle pulses for s_awready/b_push (by construction they go to IDLE next)
  ap_s_awready_pulse:    assert property (s_awready |=> !s_awready);
  ap_b_push_pulse:       assert property (b_push    |=> !b_push);

  // Functional coverage (states, transitions, and key outputs)
  cv_idle_to_cmd_en:     cover property ((state==SM_IDLE && s_awvalid) ##1 state==SM_CMD_EN);
  cv_cmd_en_to_acc:      cover property ((state==SM_CMD_EN && m_awready &&  next_pending                ) ##1 state==SM_CMD_ACCEPTED);
  cv_cmd_en_to_done:     cover property ((state==SM_CMD_EN && m_awready && !next_pending &&  b_full     ) ##1 state==SM_DONE_WAIT);
  cv_cmd_en_to_idle:     cover property ((state==SM_CMD_EN && m_awready && !next_pending && !b_full     ) ##1 state==SM_IDLE);
  cv_acc_to_cmd_en:      cover property ( state==SM_CMD_ACCEPTED ##1 state==SM_CMD_EN);
  cv_done_to_idle:       cover property ((state==SM_DONE_WAIT && !b_full) ##1 state==SM_IDLE);
  cv_done_hold:          cover property ((state==SM_DONE_WAIT &&  b_full) ##1 state==SM_DONE_WAIT);

  cv_s_awready_pulse:    cover property (s_awready);
  cv_b_push_pulse:       cover property (b_push);
  cv_next_acc:           cover property (state==SM_CMD_ACCEPTED && next);
  cv_next_cmd_en_idle:   cover property ((state==SM_CMD_EN    && m_awready && !next_pending && !b_full) && next);
  cv_next_done_idle:     cover property ((state==SM_DONE_WAIT && !b_full) && next);

endmodule

// Bind into DUT (accessing internal state and next_state)
bind axi_protocol_converter_v2_1_8_b2s_wr_cmd_fsm
  axi_protocol_converter_v2_1_8_b2s_wr_cmd_fsm_sva
  sva_i (
    .clk        (clk),
    .reset      (reset),
    .s_awvalid  (s_awvalid),
    .m_awready  (m_awready),
    .next_pending(next_pending),
    .b_full     (b_full),
    .s_awready  (s_awready),
    .m_awvalid  (m_awvalid),
    .next       (next),
    .b_push     (b_push),
    .a_push     (a_push),
    .state      (state),
    .next_state (next_state)
  );