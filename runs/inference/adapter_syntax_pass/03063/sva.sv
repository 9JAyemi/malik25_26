module simplified_axi_protocol_converter_sva (
    input logic si_rs_awvalid,
    input logic [47:0] m_payload_i_reg,
    input logic [1:0] state_reg,
    input logic [11:0] axaddr_incr,
    input logic next,
    input logic aclk,
    input logic [0:0] Q,
    input logic [3:0] S,
    input logic [11:0] m_axi_awaddr,
    input logic [3:0] wrap_second_len_r_reg,
    input logic next_pending_r_reg
);

    // S captures the upper-nibble of m_payload_i_reg on awvalid.
    check_s_captures_upper_nibble: assert property (
        @(posedge aclk) si_rs_awvalid |=> (S == $past(m_payload_i_reg[47:44]))
    );

    // S holds its value when awvalid is low.
    check_s_holds_without_awvalid: assert property (
        @(posedge aclk) !si_rs_awvalid |=> (S == $past(S))
    );

    // Q captures m_payload_i_reg[39] when the bit changes.
    check_q_captures_bit39_on_change: assert property (
        @(posedge aclk) (m_payload_i_reg[39] != $past(m_payload_i_reg[39])) |=> (Q == $past(m_payload_i_reg[39:39]))
    );

    // Q holds its value when m_payload_i_reg[39] does not change.
    check_q_holds_without_change: assert property (
        @(posedge aclk) (m_payload_i_reg[39] == $past(m_payload_i_reg[39])) |=> (Q == $past(Q))
    );

    // m_axi_awaddr increments by axaddr_incr when axaddr_incr is non-zero.
    check_awaddr_increments_when_nonzero: assert property (
        @(posedge aclk) (axaddr_incr != 12'h000) |=> (m_axi_awaddr == ($past(m_axi_awaddr) + $past(axaddr_incr)))
    );

    // m_axi_awaddr holds when axaddr_incr is zero.
    check_awaddr_holds_when_zero: assert property (
        @(posedge aclk) (axaddr_incr == 12'h000) |=> (m_axi_awaddr == $past(m_axi_awaddr))
    );

    // wrap_second_len_r_reg captures state_reg[1:0] when state_reg[1] changes.
    check_wrap_second_len_captures_on_state1_change: assert property (
        @(posedge aclk) ($past(state_reg[1]) != state_reg[1]) |=> (wrap_second_len_r_reg == $past(state_reg[1:0]))
    );

    // wrap_second_len_r_reg holds when state_reg[1] does not change.
    check_wrap_second_len_holds_without_state1_change: assert property (
        @(posedge aclk) ($past(state_reg[1]) == state_reg[1]) |=> (wrap_second_len_r_reg == $past(wrap_second_len_r_reg))
    );

    // next_pending_r_reg captures next when next changes.
    check_next_pending_captures_on_next_change: assert property (
        @(posedge aclk) ($past(next) != next) |=> (next_pending_r_reg == $past(next))
    );

    // next_pending_r_reg holds when next does not change.
    check_next_pending_holds_without_next_change: assert property (
        @(posedge aclk) ($past(next) == next) |=> (next_pending_r_reg == $past(next_pending_r_reg))
    );

endmodule