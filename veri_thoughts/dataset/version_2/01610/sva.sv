module axis_pulse_generator_sva (
    input logic        aclk,
    input logic        aresetn,
    // Slave side
    input logic        s_axis_tready,
    input logic [63:0] s_axis_tdata,
    input logic        s_axis_tvalid,
    // Master side
    input logic        m_axis_tready,
    input logic [15:0] m_axis_tdata,
    input logic        m_axis_tvalid
);
    ///// Reset behavior /////
    // While reset is asserted low, s_axis_tready must be HIGH.
    reset_ready_high: assert property (
        @(posedge aclk) !aresetn |-> (s_axis_tready == 1'b1)
    );

    ///// Combinational relationships /////
    // m_axis_tvalid is exactly s_axis_tready AND s_axis_tvalid (same cycle).
    check_tvalid_definition: assert property (
        @(posedge aclk) disable iff (!aresetn) m_axis_tvalid == (s_axis_tready & s_axis_tvalid)
    );

    // When s_axis_tvalid is LOW, m_axis_tvalid must be LOW.
    check_tvalid_low_when_s_valid_low: assert property (
        @(posedge aclk) disable iff (!aresetn) (!s_axis_tvalid) |-> (!m_axis_tvalid)
    );

    // When s_axis_tready is LOW, m_axis_tvalid must be LOW.
    check_tvalid_low_when_not_ready: assert property (
        @(posedge aclk) disable iff (!aresetn) (!s_axis_tready) |-> (!m_axis_tvalid)
    );

    // When s_axis_tready is HIGH, m_axis_tvalid mirrors s_axis_tvalid.
    check_valid_eq_when_ready: assert property (
        @(posedge aclk) disable iff (!aresetn) s_axis_tready |-> (m_axis_tvalid == s_axis_tvalid)
    );

    // When s_axis_tvalid is HIGH, m_axis_tvalid mirrors s_axis_tready.
    check_valid_eq_when_s_valid: assert property (
        @(posedge aclk) disable iff (!aresetn) s_axis_tvalid |-> (m_axis_tvalid == s_axis_tready)
    );

    // m_axis_tdata always passes through s_axis_tdata[15:0] (no latency).
    check_data_passthrough: assert property (
        @(posedge aclk) disable iff (!aresetn) m_axis_tdata == s_axis_tdata[15:0]
    );

    // When m_axis_tvalid is HIGH, data must equal s_axis_tdata[15:0] in the same cycle.
    check_data_when_valid: assert property (
        @(posedge aclk) disable iff (!aresetn) m_axis_tvalid |-> (m_axis_tdata == s_axis_tdata[15:0])
    );

    // If m_axis_tvalid is HIGH, both s_axis_tvalid and s_axis_tready must be HIGH.
    check_m_valid_implies_s_valid_and_ready: assert property (
        @(posedge aclk) disable iff (!aresetn) m_axis_tvalid |-> (s_axis_tvalid && s_axis_tready)
    );
endmodule