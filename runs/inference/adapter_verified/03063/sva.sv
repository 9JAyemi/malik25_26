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

// S captures the upper nibble of m_payload_i_reg on the next cycle.
    check_s_capture: assert property (
        @(posedge aclk) si_rs_awvalid |=> (S == $past(m_payload_i_reg[47:44]))
    );

// S holds its value when si_rs_awvalid is low.
    check_s_hold: assert property (
        @(posedge aclk) !si_rs_awvalid |=> (S == $past(S))
    );

// next_pending_r_reg is set to 1 on the next cycle when next is high.
    check_next_pending_set: assert property (
        @(posedge aclk) next |=> (next_pending_r_reg == 1'b1)
    );

// next_pending_r_reg is cleared to 0 on the next cycle when next is low.
    check_next_pending_clear: assert property (
        @(posedge aclk) !next |=> (next_pending_r_reg == 1'b0)
    );

// m_axi_awaddr increments by axaddr_incr on the next cycle when axaddr_incr is non-zero.
    check_awaddr_increment: assert property (
        @(posedge aclk) (axaddr_incr != 12'h000) |=> (m_axi_awaddr == ($past(m_axi_awaddr) + $past(axaddr_incr)))
    );

// m_axi_awaddr holds its value when axaddr_incr is zero.
    check_awaddr_hold: assert property (
        @(posedge aclk) (axaddr_incr == 12'h000) |=> (m_axi_awaddr == $past(m_axi_awaddr))
    );

// Q captures m_payload_i_reg[39] on the next cycle when bit 39 changes.
    check_q_capture_on_bit39_change: assert property (
        @(posedge aclk) (m_payload_i_reg[39] != $past(m_payload_i_reg[39])) |=> (Q == $past(m_payload_i_reg[39:39]))
    );

// Q holds its value when bit 39 does not change.
    check_q_hold_on_bit39_stable: assert property (
        @(posedge aclk) (m_payload_i_reg[39] == $past(m_payload_i_reg[39])) |=> (Q == $past(Q))
    );

// wrap_second_len_r_reg captures state_reg[1:0] on the next cycle when state_reg[1] changes.
    check_wrap_second_capture_on_state1_change: assert property (
        @(posedge aclk) (state_reg[1] != $past(state_reg[1])) |=> (wrap_second_len_r_reg == $past(state_reg[1:0]))
    );

// wrap_second_len_r_reg holds its value when state_reg[1] does not change.
    check_wrap_second_hold_on_state1_stable: assert property (
        @(posedge aclk) (state_reg[1] == $past(state_reg[1])) |=> (wrap_second_len_r_reg == $past(wrap_second_len_r_reg))
    );

endmodule
