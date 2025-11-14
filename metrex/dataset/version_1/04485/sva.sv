// SVA for axis_frame_join
// Bind this checker to the DUT. Focused, high‑quality protocol and functional checks with useful coverage.

module axis_frame_join_sva #(
    parameter S_COUNT    = 4,
    parameter DATA_WIDTH = 8,
    parameter TAG_ENABLE = 1,
    parameter TAG_WIDTH  = 16
)(
    input  logic                          clk,
    input  logic                          rst,

    input  logic [S_COUNT*DATA_WIDTH-1:0] s_axis_tdata,
    input  logic [S_COUNT-1:0]            s_axis_tvalid,
    input  logic [S_COUNT-1:0]            s_axis_tready,
    input  logic [S_COUNT-1:0]            s_axis_tlast,
    input  logic [S_COUNT-1:0]            s_axis_tuser,

    input  logic [DATA_WIDTH-1:0]         m_axis_tdata,
    input  logic                          m_axis_tvalid,
    input  logic                          m_axis_tready,
    input  logic                          m_axis_tlast,
    input  logic                          m_axis_tuser,

    input  logic [TAG_WIDTH-1:0]          tag,

    input  logic                          busy,

    // internal from DUT
    input  logic [1:0]                    state_reg,
    input  logic                          m_axis_tready_int_reg,
    input  logic                          m_axis_tready_int_early,
    input  logic [DATA_WIDTH-1:0]         m_axis_tdata_int,
    input  logic                          m_axis_tvalid_int,
    input  logic                          m_axis_tlast_int,
    input  logic                          m_axis_tuser_int,
    input  logic                          m_axis_tvalid_reg,
    input  logic                          temp_m_axis_tvalid_reg,
    input  logic [$clog2(S_COUNT)-1:0]    port_sel_reg,
    input  logic [$clog2((TAG_WIDTH + DATA_WIDTH - 1)/DATA_WIDTH)-1:0] frame_ptr_reg
);

    localparam CL_S_COUNT       = $clog2(S_COUNT);
    localparam TAG_WORD_WIDTH   = (TAG_WIDTH + DATA_WIDTH - 1) / DATA_WIDTH;
    localparam CL_TAG_WORD_WIDTH= $clog2(TAG_WORD_WIDTH);

    localparam [1:0]
        STATE_IDLE       = 2'd0,
        STATE_WRITE_TAG  = 2'd1,
        STATE_TRANSFER   = 2'd2;

    default clocking cb @(posedge clk); endclocking
    default disable iff (rst);

    // Helpers
    function automatic logic [DATA_WIDTH-1:0] slice(input logic [S_COUNT*DATA_WIDTH-1:0] vec, input int idx);
        slice = vec[idx*DATA_WIDTH +: DATA_WIDTH];
    endfunction

    // 1) Output AXIS stability under backpressure
    assert property (m_axis_tvalid && !m_axis_tready |=> m_axis_tvalid && $stable({m_axis_tdata,m_axis_tlast,m_axis_tuser}))
        else $error("m_axis signals changed while !m_axis_tready");

    // 2) m_axis_tuser only with last
    assert property (m_axis_tuser |-> m_axis_tlast)
        else $error("m_axis_tuser asserted without m_axis_tlast");

    // 3) busy reflects state!=IDLE
    assert property (busy == (state_reg != STATE_IDLE))
        else $error("busy inconsistent with state");

    // 4) Reset conditions in IDLE
    assert property (state_reg == STATE_IDLE |-> port_sel_reg == '0)
        else $error("port_sel_reg not zero in IDLE");
    if (TAG_ENABLE) begin
        assert property (state_reg == STATE_IDLE |-> frame_ptr_reg == '0)
            else $error("frame_ptr_reg not zero in IDLE");
    end

    // 5) s_axis_tready onehot0
    assert property ($onehot0(s_axis_tready))
        else $error("s_axis_tready not onehot0");

    // 6) s_axis_tready index discipline
    assert property ((|s_axis_tready) && state_reg == STATE_TRANSFER |-> s_axis_tready == (1'b1 << port_sel_reg))
        else $error("s_axis_tready not pointing to port_sel in TRANSFER");

    if (TAG_ENABLE) begin
        // In IDLE with TAG enabled, no s_axis ready
        assert property (state_reg == STATE_IDLE |-> s_axis_tready == '0)
            else $error("s_axis_tready asserted in IDLE when TAG_ENABLE=1");

        // In WRITE_TAG, only bit 0 may be asserted (or none)
        assert property (state_reg == STATE_WRITE_TAG |-> (s_axis_tready == '0 || s_axis_tready == (1'b1 << 0)))
            else $error("s_axis_tready invalid during WRITE_TAG");

        // Tag progress bounds
        if (TAG_WORD_WIDTH > 0) begin
            assert property (state_reg == STATE_WRITE_TAG |-> frame_ptr_reg < TAG_WORD_WIDTH)
                else $error("frame_ptr out of range during WRITE_TAG");
        end

        // Exit WRITE_TAG to TRANSFER after last tag word accepted internally
        if (TAG_WORD_WIDTH > 0) begin
            assert property ($past(state_reg == STATE_WRITE_TAG && m_axis_tready_int_reg && (frame_ptr_reg == TAG_WORD_WIDTH-1)) |-> state_reg == STATE_TRANSFER)
                else $error("Did not transition to TRANSFER after final tag word");
        end
    end else begin
        // If TAG disabled, never be in WRITE_TAG
        assert property (state_reg != STATE_WRITE_TAG)
            else $error("Entered WRITE_TAG while TAG_ENABLE=0");

        // In IDLE with TAG disabled, only port 0 may be ready when any ready
        assert property (state_reg == STATE_IDLE && (|s_axis_tready) |-> s_axis_tready == (1'b1 << 0))
            else $error("s_axis_tready not limited to port 0 in IDLE when TAG_ENABLE=0");
    end

    // 7) TRANSFER data routing and last behavior
    genvar gi;
    generate
        for (gi = 0; gi < S_COUNT; gi = gi+1) begin : G_PORT_CHK
            // Internal path data correctness when accepting from input
            assert property (state_reg == STATE_TRANSFER &&
                             s_axis_tready[gi] && s_axis_tvalid[gi] && (port_sel_reg == gi) && m_axis_tready_int_reg
                             |->
                             m_axis_tvalid_int && m_axis_tdata_int == slice(s_axis_tdata, gi))
                else $error("m_axis_tdata_int mismatch with selected s_axis_tdata");

            // Last behavior and port increment/finalization
            if (gi < S_COUNT-1) begin
                // Not final port: last on input must NOT assert output last, and port_sel must advance
                assert property (state_reg == STATE_TRANSFER &&
                                 s_axis_tready[gi] && s_axis_tvalid[gi] && s_axis_tlast[gi] && (port_sel_reg == gi) && m_axis_tready_int_reg
                                 |->
                                 !m_axis_tlast_int)
                    else $error("m_axis_tlast_int asserted before final port");
                assert property (state_reg == STATE_TRANSFER &&
                                 s_axis_tready[gi] && s_axis_tvalid[gi] && s_axis_tlast[gi] && (port_sel_reg == gi) && m_axis_tready_int_reg
                                 |=> port_sel_reg == gi+1)
                    else $error("port_sel did not advance after port last");
            end else begin
                // Final port: last on input must assert output last and return to IDLE next
                assert property (state_reg == STATE_TRANSFER &&
                                 s_axis_tready[gi] && s_axis_tvalid[gi] && s_axis_tlast[gi] && (port_sel_reg == gi) && m_axis_tready_int_reg
                                 |->
                                 m_axis_tlast_int)
                    else $error("m_axis_tlast_int not asserted on final port last");
                assert property (state_reg == STATE_TRANSFER &&
                                 s_axis_tready[gi] && s_axis_tvalid[gi] && s_axis_tlast[gi] && (port_sel_reg == gi) && m_axis_tready_int_reg
                                 |=> state_reg == STATE_IDLE)
                    else $error("Did not return to IDLE after final port last");
            end
        end
    endgenerate

    // 8) Output handshake with last returns to IDLE next cycle
    assert property (m_axis_tvalid && m_axis_tready && m_axis_tlast |=> state_reg == STATE_IDLE)
        else $error("State not IDLE after output last handshake");

    // 9) Ready pipeline/early ready invariant: cannot assert early ready if both outputs occupied and int valid asserted
    assert property (m_axis_tready_int_early |-> (m_axis_tready || (!temp_m_axis_tvalid_reg && (!m_axis_tvalid_reg || !m_axis_tvalid_int))))
        else $error("m_axis_tready_int_early invariant violated");

    // Coverage

    // A) Skid buffer exercised
    cover property (m_axis_tvalid && !m_axis_tready ##1 m_axis_tvalid && !m_axis_tready ##1 m_axis_tvalid && m_axis_tready);

    // B) Output last observed
    cover property (m_axis_tvalid && m_axis_tready && m_axis_tlast);

    // C) TUSER at last observed
    cover property (m_axis_tvalid && m_axis_tready && m_axis_tlast && m_axis_tuser);

    // D) Tag path (if enabled): IDLE -> WRITE_TAG -> TRANSFER
    if (TAG_ENABLE) begin
        cover property (state_reg == STATE_IDLE && (|s_axis_tvalid)
                        ##1 state_reg == STATE_WRITE_TAG
                        ##[1:$] state_reg == STATE_TRANSFER);
    end

    // E) No-tag path (if disabled): IDLE -> TRANSFER
    if (!TAG_ENABLE) begin
        cover property (state_reg == STATE_IDLE && (|s_axis_tvalid)
                        ##1 state_reg == STATE_TRANSFER);
    end

    // F) Multi-port progression observed
    if (S_COUNT > 1) begin
        cover property (state_reg == STATE_TRANSFER && port_sel_reg == 0
                        ##[1:$] state_reg == STATE_TRANSFER && port_sel_reg == S_COUNT-1);
    end

    // G) Busy pulse for one full frame
    cover property ($rose(busy) ##[1:$] m_axis_tvalid && m_axis_tready && m_axis_tlast ##1 !busy);

endmodule

// Bind into DUT
bind axis_frame_join axis_frame_join_sva #(
    .S_COUNT(S_COUNT),
    .DATA_WIDTH(DATA_WIDTH),
    .TAG_ENABLE(TAG_ENABLE),
    .TAG_WIDTH(TAG_WIDTH)
) axis_frame_join_sva_i (
    .clk                       (clk),
    .rst                       (rst),
    .s_axis_tdata              (s_axis_tdata),
    .s_axis_tvalid             (s_axis_tvalid),
    .s_axis_tready             (s_axis_tready),
    .s_axis_tlast              (s_axis_tlast),
    .s_axis_tuser              (s_axis_tuser),
    .m_axis_tdata              (m_axis_tdata),
    .m_axis_tvalid             (m_axis_tvalid),
    .m_axis_tready             (m_axis_tready),
    .m_axis_tlast              (m_axis_tlast),
    .m_axis_tuser              (m_axis_tuser),
    .tag                       (tag),
    .busy                      (busy),
    // internals
    .state_reg                 (state_reg),
    .m_axis_tready_int_reg     (m_axis_tready_int_reg),
    .m_axis_tready_int_early   (m_axis_tready_int_early),
    .m_axis_tdata_int          (m_axis_tdata_int),
    .m_axis_tvalid_int         (m_axis_tvalid_int),
    .m_axis_tlast_int          (m_axis_tlast_int),
    .m_axis_tuser_int          (m_axis_tuser_int),
    .m_axis_tvalid_reg         (m_axis_tvalid_reg),
    .temp_m_axis_tvalid_reg    (temp_m_axis_tvalid_reg),
    .port_sel_reg              (port_sel_reg),
    .frame_ptr_reg             (frame_ptr_reg)
);