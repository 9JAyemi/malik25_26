module simplified_axi_protocol_converter_sva (
    input logic aclk,
    input logic si_rs_awvalid,
    input logic [47:0] m_payload_i_reg,
    input logic [1:0] state_reg,
    input logic [11:0] axaddr_incr,
    input logic next,
    output logic Q,
    output logic [3:0] S,
    output logic [11:0] m_axi_awaddr,
    output logic [3:0] wrap_second_len_r_reg,
    output logic next_pending_r_reg
);
    // Q is set to the most significant bit of m_payload_i_reg when si_rs_awvalid is asserted
    property p_Q_set;
        @(posedge aclk) disable iff (!si_rs_awvalid) Q == m_payload_i_reg[39:39];
    endproperty
    assert property (p_Q_set) else $error("Q is not set correctly when si_rs_awvalid is asserted");

    // S is set to bits 47:44 of m_payload_i_reg when si_rs_awvalid is asserted
    property p_S_set;
        @(posedge aclk) disable iff (!si_rs_awvalid) S == m_payload_i_reg[47:44];
    endproperty
    assert property (p_S_set) else $error("S is not set correctly when si_rs_awvalid is asserted");

    // m_axi_awaddr increments by axaddr_incr when axaddr_incr is non-zero
    property p_m_axi_awaddr_increment;
        @(posedge aclk) disable iff (!axaddr_incr) m_axi_awaddr == m_axi_awaddr + axaddr_incr;
    endproperty
    assert property (p_m_axi_awaddr_increment) else $error("m_axi_awaddr is not incremented correctly");

    // next_pending_r_reg is set to 1 when next is asserted
    property p_next_pending_r_reg_set;
        @(posedge aclk) disable iff (!next) next_pending_r_reg == 1'b1;
    endproperty
    assert property (p_next_pending_r_reg_set) else $error("next_pending_r_reg is not set correctly when next is asserted");

    // wrap_second_len_r_reg is set to state_reg[1:0] when state_reg[1] changes
    property p_wrap_second_len_r_reg_set;
        @(posedge aclk) disable iff (!state_reg[1]) wrap_second_len_r_reg == state_reg[1:0];
    endproperty
    assert property (p_wrap_second_len_r_reg_set) else $error("wrap_second_len_r_reg is not set correctly when state_reg[1] changes");

    // Q is set to the most significant bit of m_payload_i_reg when m_payload_i_reg[39] changes
    property p_Q_on_m_payload_i_reg_change;
        @(posedge aclk) disable iff (!m_payload_i_reg[39]) Q == m_payload_i_reg[39:39];
    endproperty
    assert property (p_Q_on_m_payload_i_reg_change) else $error("Q is not set correctly when m_payload_i_reg[39] changes");

    // next_pending_r_reg is set to the value of next when next changes
    property p_next_pending_r_reg_on_next_change;
        @(posedge aclk) disable iff (!next) next_pending_r_reg == next;
    endproperty
    assert property (p_next_pending_r_reg_on_next_change) else $error("next_pending_r_reg is not set correctly when next changes");

    // wrap_second_len_r_reg is set to state_reg[1:0] when state_reg[1] changes
    property p_wrap_second_len_r_reg_on_state_reg_change;
        @(posedge aclk) disable iff (!state_reg[1]) wrap_second_len_r_reg == state_reg[1:0];
    endproperty
    assert property (p_wrap_second_len_r_reg_on_state_reg_change) else $error("wrap_second_len_r_reg is not set correctly when state_reg[1] changes");

    // Q is set to the most significant bit of m_payload_i_reg when m_payload_i_reg[39] changes
    property p_Q_on_m_payload_i_reg_change_2;
        @(posedge aclk) disable iff (!m_payload_i_reg[39]) Q == m_payload_i_reg[39:39];
    endproperty
    assert property (p_Q_on_m_payload_i_reg_change_2) else $error("Q is not set correctly when m_payload_i_reg[39] changes");

    // next_pending_r_reg is set to the value of next when next changes
    property p_next_pending_r_reg_on_next_change_2;
        @(posedge aclk) disable iff (!next) next_pending_r_reg == next;
    endproperty
    assert property (p_next_pending_r_reg_on_next_change_2) else $error("next_pending_r_reg is not set correctly when next changes");
endmodule