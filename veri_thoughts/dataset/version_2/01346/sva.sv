module axi_to_custom_protocol_converter_sva
(
    input logic next_pending_r_reg,
    input logic [11:0] m_axi_awaddr,
    input logic [47:0] m_payload_i_reg,
    input logic incr_next_pending,
    input logic wrap_next_pending,
    input logic sel_first_reg_0,
    input logic aclk,
    input logic [11:0] m_axi_awaddr_in,
    input logic [47:0] m_payload_i_reg_in,
    input logic next,
    input logic incr_next_pending_in,
    input logic wrap_next_pending_in,
    input logic sel_first_i
);
    // On sel_first_i, load AWADDR/PAYLOAD from inputs, raise sel_first_reg_0, and clear next_pending_r_reg.
    check_sel_first_loads: assert property (
        @(posedge aclk) sel_first_i |-> (m_axi_awaddr == m_axi_awaddr_in)
                                   && (m_payload_i_reg == m_payload_i_reg_in)
                                   && (sel_first_reg_0 == 1'b1)
                                   && (next_pending_r_reg == 1'b0)
    );

    // sel_first_reg_0 mirrors sel_first_i every cycle.
    check_sel_first_flag_mirror: assert property (
        @(posedge aclk) sel_first_reg_0 == sel_first_i
    );

    // In incr branch, set incr_next_pending=1, wrap_next_pending=0, and clear next_pending_r_reg.
    check_incr_branch_flags: assert property (
        @(posedge aclk) (!sel_first_i && incr_next_pending_in) |-> (incr_next_pending == 1'b1)
                                                                  && (wrap_next_pending == 1'b0)
                                                                  && (next_pending_r_reg == 1'b0)
    );

    // In wrap branch, load AWADDR from input, set wrap_next_pending=1, incr_next_pending=0, and clear next_pending_r_reg.
    check_wrap_branch_effects: assert property (
        @(posedge aclk) (!sel_first_i && !incr_next_pending_in && wrap_next_pending_in) |-> (m_axi_awaddr == m_axi_awaddr_in)
                                                                                           && (wrap_next_pending == 1'b1)
                                                                                           && (incr_next_pending == 1'b0)
                                                                                           && (next_pending_r_reg == 1'b0)
    );

    // In next branch, clear incr_next_pending, wrap_next_pending, and next_pending_r_reg.
    check_next_branch_effects: assert property (
        @(posedge aclk) (!sel_first_i && !incr_next_pending_in && !wrap_next_pending_in && next) |-> (incr_next_pending == 1'b0)
                                                                                                  && (wrap_next_pending == 1'b0)
                                                                                                  && (next_pending_r_reg == 1'b0)
    );

    // Payload holds its value whenever sel_first_i stays LOW across consecutive cycles.
    check_payload_holds_when_sel_first_low: assert property (
        @(posedge aclk) ($past(!sel_first_i) && !sel_first_i) |-> (m_payload_i_reg == $past(m_payload_i_reg))
    );

    // AWADDR holds when there is no incr or wrap in two consecutive cycles with sel_first_i LOW.
    check_addr_holds_when_no_update: assert property (
        @(posedge aclk) ($past(!sel_first_i && !incr_next_pending_in && !wrap_next_pending_in)
                         && !sel_first_i && !incr_next_pending_in && !wrap_next_pending_in)
                         |-> (m_axi_awaddr == $past(m_axi_awaddr))
    );

    // Flags and next_pending_r_reg hold when idle (no incr/wrap/next) across two consecutive cycles with sel_first_i LOW.
    check_flags_hold_when_idle: assert property (
        @(posedge aclk) ($past(!sel_first_i && !incr_next_pending_in && !wrap_next_pending_in && !next)
                         && !sel_first_i && !incr_next_pending_in && !wrap_next_pending_in && !next)
                         |-> (incr_next_pending == $past(incr_next_pending))
                          && (wrap_next_pending == $past(wrap_next_pending))
                          && (next_pending_r_reg == $past(next_pending_r_reg))
    );
endmodule