module axi_protocol_converter_sva (
    input logic aclk,
    input logic m_axi_arvalid,
    input logic m_axi_arready,
    input logic [31:0] m_axi_araddr,
    input logic [31:0] m_payload_i_reg,
    input logic [31:0] m_payload_o_reg,
    input logic si_rs_arvalid
);
    // m_axi_arready high pulses must be single-cycle.
    ready_pulse_single_cycle: assert property (
        @(posedge aclk) $rose(m_axi_arready) |-> ##1 !m_axi_arready
    );

    // m_payload_o_reg can change only in cycles when m_axi_arready is HIGH.
    payload_update_only_when_ready: assert property (
        @(posedge aclk) $changed(m_payload_o_reg) |-> (m_axi_arready == 1'b1)
    );

    // When m_axi_arready is LOW in a cycle, m_payload_o_reg must not change that cycle.
    payload_no_update_when_ready_low: assert property (
        @(posedge aclk) (m_axi_arready == 1'b0) |-> !$changed(m_payload_o_reg)
    );

    // m_payload_o_reg must not update in two consecutive cycles.
    payload_no_back_to_back_updates: assert property (
        @(posedge aclk) $changed(m_payload_o_reg) |-> ##1 !$changed(m_payload_o_reg)
    );

    // After a payload update, m_axi_arready must be LOW in the next cycle.
    payload_update_implies_ready_low_next: assert property (
        @(posedge aclk) $changed(m_payload_o_reg) |-> ##1 (m_axi_arready == 1'b0)
    );

    // If m_axi_arready is HIGH, m_payload_o_reg holds its value into the next cycle.
    ready_high_payload_stable_next: assert property (
        @(posedge aclk) (m_axi_arready == 1'b1) |-> ##1 $stable(m_payload_o_reg)
    );
endmodule