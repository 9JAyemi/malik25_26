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

    // S captures the upper bits of m_payload_i_reg on the next cycle.
    check_s_captures_m_payload_bits: assert property (
        @(posedge aclk) si_rs_awvalid |=> (S == $past(m_payload_i_reg[47:44]))
    );

    // S holds its value when si_rs_awvalid is low.
    check_s_holds_without_awvalid: assert property (
        @(posedge aclk) !si_rs_awvalid |=> (S == $past(S))
    );

    // m_axi_awaddr increments by axaddr_incr when axaddr_incr is non-zero.
    check_awaddr_increments_on_nonzero_axaddr_incr: assert property (
        @(posedge aclk) (axaddr_incr != 12'd0) |=> (m_axi_awaddr == ($past(m_axi_awaddr) + $past(axaddr_incr)))
    );

    // m_axi_awaddr holds when axaddr_incr is zero.
    check_awaddr_holds_on_zero_axaddr_incr: assert property (
        @(posedge aclk) (axaddr_incr == 12'd0) |=> (m_axi_awaddr == $past(m_axi_awaddr))
    );

    // Q captures m_payload_i_reg[39] when the prior MSB differs from the previous cycle.
    check_q_captures_msb_change: assert property (
        @(posedge aclk) ($past(m_payload_i_reg[39]) != $past(m_payload_i_reg[39], 2)) |=> (Q == $past(m_payload_i_reg[39], 1))
    );

    // Q holds when the prior MSB does not differ from the previous cycle.
    check_q_holds_on_msb_stable: assert property (
        @(posedge aclk) ($past(m_payload_i_reg[39]) == $past(m_payload_i_reg[39], 2)) |=> (Q == $past(Q))
    );

    // wrap_second_len_r_reg captures state_reg[1:0] when state_reg[1] differs from the previous cycle.
    check_wrap_second_len_captures_state_change: assert property (
        @(posedge aclk) ($past(state_reg[1]) != $past(state_reg[1], 2)) |=> (wrap_second_len_r_reg == $past(state_reg[1:0], 1))
    );

    // wrap_second_len_r_reg holds when state_reg[1] does not differ from the previous cycle.
    check_wrap_second_len_holds_on_state_stable: assert property (
        @(posedge aclk) ($past(state_reg[1]) == $past(state_reg[1], 2)) |=> (wrap_second_len_r_reg == $past(wrap_second_len_r_reg))
    );

    // next_pending_r_reg captures next when next differs from the previous cycle.
    check_next_pending_r_captures_next_change: assert property (
        @(posedge aclk) ($past(next) != $past(next, 2)) |=> (next_pending_r_reg == $past(next, 1))
    );

    // next_pending_r_reg holds when next does not differ from the previous cycle.
    check_next_pending_r_holds_on_next_stable: assert property (
        @(posedge aclk) ($past(next) == $past(next, 2)) |=> (next_pending_r_reg == $past(next_pending_r_reg))
    );

endmodule