module simplified_axi_protocol_converter_sva (
    input logic        si_rs_awvalid,
    input logic [47:0] m_payload_i_reg,
    input logic [1:0]  state_reg,
    input logic [11:0] axaddr_incr,
    input logic        next,
    input logic        aclk,
    input logic [0:0]  Q,
    input logic [3:0]  S,
    input logic [11:0] m_axi_awaddr,
    input logic [3:0]  wrap_second_len_r_reg,
    input logic        next_pending_r_reg
);

    // S captures m_payload_i_reg[47:44] when si_rs_awvalid is high.
    check_s_capture_on_valid: assert property (
        @(posedge aclk) disable iff ($initstate)
        si_rs_awvalid |=> (S == $past(m_payload_i_reg[47:44]))
    );

    // S holds its value when si_rs_awvalid is low.
    check_s_hold_without_valid: assert property (
        @(posedge aclk) disable iff ($initstate)
        !si_rs_awvalid |=> (S == $past(S))
    );

    // m_axi_awaddr increments by axaddr_incr when axaddr_incr is nonzero.
    check_awaddr_increment_on_nonzero_incr: assert property (
        @(posedge aclk) disable iff ($initstate)
        (axaddr_incr != 12'b0) |=> (m_axi_awaddr == ($past(m_axi_awaddr) + $past(axaddr_incr)))
    );

    // m_axi_awaddr holds when axaddr_incr is zero.
    check_awaddr_hold_on_zero_incr: assert property (
        @(posedge aclk) disable iff ($initstate)
        (axaddr_incr == 12'b0) |=> (m_axi_awaddr == $past(m_axi_awaddr))
    );

    // Q captures m_payload_i_reg[39] when that bit changes.
    check_q_update_on_payload_bit39_change: assert property (
        @(posedge aclk) disable iff ($initstate)
        (m_payload_i_reg[39] != $past(m_payload_i_reg[39])) |=> (Q == $past(m_payload_i_reg[39]))
    );

    // Q holds when m_payload_i_reg[39] does not change.
    check_q_hold_when_payload_bit39_stable: assert property (
        @(posedge aclk) disable iff ($initstate)
        (m_payload_i_reg[39] == $past(m_payload_i_reg[39])) |=> (Q == $past(Q))
    );

    // wrap_second_len_r_reg captures state_reg when state_reg[1] changes.
    check_wrap_len_update_on_state_bit1_change: assert property (
        @(posedge aclk) disable iff ($initstate)
        (state_reg[1] != $past(state_reg[1])) |=> (wrap_second_len_r_reg == {2'b00, $past(state_reg)})
    );

    // wrap_second_len_r_reg holds when state_reg[1] is stable.
    check_wrap_len_hold_when_state_bit1_stable: assert property (
        @(posedge aclk) disable iff ($initstate)
        (state_reg[1] == $past(state_reg[1])) |=> (wrap_second_len_r_reg == $past(wrap_second_len_r_reg))
    );

    // next_pending_r_reg follows next when next toggles.
    check_next_pending_follow_on_toggle: assert property (
        @(posedge aclk) disable iff ($initstate)
        (next != $past(next)) |=> (next_pending_r_reg == $past(next))
    );

    // next_pending_r_reg stays high while next remains high.
    check_next_pending_high_on_stable_high: assert property (
        @(posedge aclk) disable iff ($initstate)
        (next && $past(next)) |=> (next_pending_r_reg == 1'b1)
    );

    // next_pending_r_reg holds when next remains low.
    check_next_pending_hold_on_stable_low: assert property (
        @(posedge aclk) disable iff ($initstate)
        (!next && !$past(next)) |=> (next_pending_r_reg == $past(next_pending_r_reg))
    );

endmodule