// SVA for axis_crosspoint
// Bind or instantiate this module alongside the DUT.
// Concise end-to-end checks with 1-cycle latency, select range, and param-gated fields.

module axis_crosspoint_sva #(
    parameter S_COUNT = 4,
    parameter M_COUNT = 4,
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter LAST_ENABLE = 1,
    parameter ID_ENABLE = 0,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 0,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1
)(
    input  wire                               clk,
    input  wire                               rst,

    input  wire [S_COUNT*DATA_WIDTH-1:0]      s_axis_tdata,
    input  wire [S_COUNT*KEEP_WIDTH-1:0]      s_axis_tkeep,
    input  wire [S_COUNT-1:0]                 s_axis_tvalid,
    input  wire [S_COUNT-1:0]                 s_axis_tlast,
    input  wire [S_COUNT*ID_WIDTH-1:0]        s_axis_tid,
    input  wire [S_COUNT*DEST_WIDTH-1:0]      s_axis_tdest,
    input  wire [S_COUNT*USER_WIDTH-1:0]      s_axis_tuser,

    input  wire [M_COUNT*DATA_WIDTH-1:0]      m_axis_tdata,
    input  wire [M_COUNT*KEEP_WIDTH-1:0]      m_axis_tkeep,
    input  wire [M_COUNT-1:0]                 m_axis_tvalid,
    input  wire [M_COUNT-1:0]                 m_axis_tlast,
    input  wire [M_COUNT*ID_WIDTH-1:0]        m_axis_tid,
    input  wire [M_COUNT*DEST_WIDTH-1:0]      m_axis_tdest,
    input  wire [M_COUNT*USER_WIDTH-1:0]      m_axis_tuser,

    input  wire [M_COUNT*$clog2(S_COUNT)-1:0] select
);

localparam int CL_S_COUNT = $clog2(S_COUNT);

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

// Disabled-field constants
generate
    if (!KEEP_ENABLE && KEEP_WIDTH > 0) begin
        assert property (m_axis_tkeep == {M_COUNT*KEEP_WIDTH{1'b1}});
    end
    if (!LAST_ENABLE) begin
        assert property (m_axis_tlast == {M_COUNT{1'b1}});
    end
    if (!ID_ENABLE && ID_WIDTH > 0) begin
        assert property (m_axis_tid == {M_COUNT*ID_WIDTH{1'b0}});
    end
    if (!DEST_ENABLE && DEST_WIDTH > 0) begin
        assert property (m_axis_tdest == {M_COUNT*DEST_WIDTH{1'b0}});
    end
    if (!USER_ENABLE && USER_WIDTH > 0) begin
        assert property (m_axis_tuser == {M_COUNT*USER_WIDTH{1'b0}});
    end
endgenerate

// Select range/known checks per output
generate
    if (CL_S_COUNT > 0) begin : g_sel_checks
        genvar oi;
        for (oi = 0; oi < M_COUNT; oi++) begin : g_sel_o
            wire [CL_S_COUNT-1:0] sel_now = select[oi*CL_S_COUNT +: CL_S_COUNT];
            assert property (!$isunknown(sel_now));
            assert property (sel_now < S_COUNT);
        end
    end
endgenerate

// Functional 1-cycle routing checks per output, using $past(select)
generate
    genvar i;
    for (i = 0; i < M_COUNT; i++) begin : g_route
        if (CL_S_COUNT > 0) begin : g_route_sel
            property p_route_i;
                int unsigned sel_p;
                sel_p = $past(select[i*CL_S_COUNT +: CL_S_COUNT]);
                // data
                (m_axis_tdata[i*DATA_WIDTH +: DATA_WIDTH]
                    == $past(s_axis_tdata[sel_p*DATA_WIDTH +: DATA_WIDTH]))
                // valid
                && (m_axis_tvalid[i]
                    == $past(s_axis_tvalid[sel_p]))
                // keep
                && (KEEP_ENABLE ? (m_axis_tkeep[i*KEEP_WIDTH +: KEEP_WIDTH]
                    == $past(s_axis_tkeep[sel_p*KEEP_WIDTH +: KEEP_WIDTH])) : 1)
                // last
                && (LAST_ENABLE ? (m_axis_tlast[i]
                    == $past(s_axis_tlast[sel_p])) : 1)
                // id
                && ((ID_ENABLE && ID_WIDTH>0) ? (m_axis_tid[i*ID_WIDTH +: ID_WIDTH]
                    == $past(s_axis_tid[sel_p*ID_WIDTH +: ID_WIDTH])) : 1)
                // dest
                && ((DEST_ENABLE && DEST_WIDTH>0) ? (m_axis_tdest[i*DEST_WIDTH +: DEST_WIDTH]
                    == $past(s_axis_tdest[sel_p*DEST_WIDTH +: DEST_WIDTH])) : 1)
                // user
                && ((USER_ENABLE && USER_WIDTH>0) ? (m_axis_tuser[i*USER_WIDTH +: USER_WIDTH]
                    == $past(s_axis_tuser[sel_p*USER_WIDTH +: USER_WIDTH])) : 1);
            endproperty
            assert property (p_route_i);
        end else begin : g_route_single  // S_COUNT == 1 (no select bus)
            assert property (
                m_axis_tdata[i*DATA_WIDTH +: DATA_WIDTH]
                    == $past(s_axis_tdata[0*DATA_WIDTH +: DATA_WIDTH])
            );
            assert property (m_axis_tvalid[i] == $past(s_axis_tvalid[0]));
            if (KEEP_ENABLE && KEEP_WIDTH > 0) begin
                assert property (
                    m_axis_tkeep[i*KEEP_WIDTH +: KEEP_WIDTH]
                        == $past(s_axis_tkeep[0*KEEP_WIDTH +: KEEP_WIDTH])
                );
            end
            if (LAST_ENABLE) begin
                assert property (m_axis_tlast[i] == $past(s_axis_tlast[0]));
            end
            if (ID_ENABLE && ID_WIDTH > 0) begin
                assert property (
                    m_axis_tid[i*ID_WIDTH +: ID_WIDTH]
                        == $past(s_axis_tid[0*ID_WIDTH +: ID_WIDTH])
                );
            end
            if (DEST_ENABLE && DEST_WIDTH > 0) begin
                assert property (
                    m_axis_tdest[i*DEST_WIDTH +: DEST_WIDTH]
                        == $past(s_axis_tdest[0*DEST_WIDTH +: DEST_WIDTH])
                );
            end
            if (USER_ENABLE && USER_WIDTH > 0) begin
                assert property (
                    m_axis_tuser[i*USER_WIDTH +: USER_WIDTH]
                        == $past(s_axis_tuser[0*USER_WIDTH +: USER_WIDTH])
                );
            end
        end
    end
endgenerate

// Simple post-reset behavior: valid clears on the first cycle after reset asserted
assert property (rst |=> m_axis_tvalid == {M_COUNT{1'b0}});

// Coverage: exercise all select values and valid flow
generate
    if (CL_S_COUNT > 0) begin : g_cov
        genvar oc, sc;
        for (oc = 0; oc < M_COUNT; oc++) begin : g_cov_o
            for (sc = 0; sc < S_COUNT; sc++) begin : g_cov_s
                wire [CL_S_COUNT-1:0] sc_idx = sc[CL_S_COUNT-1:0];
                cover property (select[oc*CL_S_COUNT +: CL_S_COUNT] == sc_idx);
                cover property (s_axis_tvalid[sc] && (select[oc*CL_S_COUNT +: CL_S_COUNT] == sc_idx)
                                |=> m_axis_tvalid[oc]);
                if (LAST_ENABLE)
                    cover property (s_axis_tlast[sc] && s_axis_tvalid[sc]
                                    && (select[oc*CL_S_COUNT +: CL_S_COUNT] == sc_idx)
                                    |=> m_axis_tlast[oc]);
            end
        end
    end else begin : g_cov_single
        genvar oc2;
        for (oc2 = 0; oc2 < M_COUNT; oc2++) begin
            cover property (s_axis_tvalid[0] |=> m_axis_tvalid[oc2]);
            if (LAST_ENABLE)
                cover property (s_axis_tlast[0] && s_axis_tvalid[0] |=> m_axis_tlast[oc2]);
        end
    end
endgenerate

endmodule

// Example bind (uncomment to use):
// bind axis_crosspoint axis_crosspoint_sva #(
//   .S_COUNT(S_COUNT), .M_COUNT(M_COUNT), .DATA_WIDTH(DATA_WIDTH),
//   .KEEP_ENABLE(KEEP_ENABLE), .KEEP_WIDTH(KEEP_WIDTH), .LAST_ENABLE(LAST_ENABLE),
//   .ID_ENABLE(ID_ENABLE), .ID_WIDTH(ID_WIDTH), .DEST_ENABLE(DEST_ENABLE), .DEST_WIDTH(DEST_WIDTH),
//   .USER_ENABLE(USER_ENABLE), .USER_WIDTH(USER_WIDTH)
// ) axis_crosspoint_sva_i (.*);