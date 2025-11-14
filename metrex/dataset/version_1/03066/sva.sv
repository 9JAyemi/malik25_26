// SVA for axis_demux: concise, high-quality checks and coverage.
// Bind this module to the DUT.
// Example: bind axis_demux axis_demux_sva #(.M_COUNT(M_COUNT), .DATA_WIDTH(DATA_WIDTH), .KEEP_ENABLE(KEEP_ENABLE), .KEEP_WIDTH(KEEP_WIDTH), .ID_ENABLE(ID_ENABLE), .ID_WIDTH(ID_WIDTH), .DEST_ENABLE(DEST_ENABLE), .DEST_WIDTH(DEST_WIDTH), .USER_ENABLE(USER_ENABLE), .USER_WIDTH(USER_WIDTH)) i_axis_demux_sva (.*);

module axis_demux_sva #
(
    parameter M_COUNT = 4,
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter ID_ENABLE = 0,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 0,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1
)
(
    input  wire                          clk,
    input  wire                          rst,

    input  wire [DATA_WIDTH-1:0]         s_axis_tdata,
    input  wire [KEEP_WIDTH-1:0]         s_axis_tkeep,
    input  wire                          s_axis_tvalid,
    output wire                          s_axis_tready,
    input  wire                          s_axis_tlast,
    input  wire [ID_WIDTH-1:0]           s_axis_tid,
    input  wire [DEST_WIDTH-1:0]         s_axis_tdest,
    input  wire [USER_WIDTH-1:0]         s_axis_tuser,

    output wire [M_COUNT*DATA_WIDTH-1:0] m_axis_tdata,
    output wire [M_COUNT*KEEP_WIDTH-1:0] m_axis_tkeep,
    output wire [M_COUNT-1:0]            m_axis_tvalid,
    input  wire [M_COUNT-1:0]            m_axis_tready,
    output wire [M_COUNT-1:0]            m_axis_tlast,
    output wire [M_COUNT*ID_WIDTH-1:0]   m_axis_tid,
    output wire [M_COUNT*DEST_WIDTH-1:0] m_axis_tdest,
    output wire [M_COUNT*USER_WIDTH-1:0] m_axis_tuser,

    input  wire                          enable,
    input  wire                          drop,
    input  wire [$clog2(M_COUNT)-1:0]    select
);

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

// Helpers
function automatic logic [DATA_WIDTH-1:0] data_slice(input logic [M_COUNT*DATA_WIDTH-1:0] bus, input int unsigned i);
    return bus[i*DATA_WIDTH +: DATA_WIDTH];
endfunction
function automatic logic [KEEP_WIDTH-1:0] keep_slice(input logic [M_COUNT*KEEP_WIDTH-1:0] bus, input int unsigned i);
    return bus[i*KEEP_WIDTH +: KEEP_WIDTH];
endfunction
function automatic logic [ID_WIDTH-1:0] id_slice(input logic [M_COUNT*ID_WIDTH-1:0] bus, input int unsigned i);
    return bus[i*ID_WIDTH +: ID_WIDTH];
endfunction
function automatic logic [DEST_WIDTH-1:0] dest_slice(input logic [M_COUNT*DEST_WIDTH-1:0] bus, input int unsigned i);
    return bus[i*DEST_WIDTH +: DEST_WIDTH];
endfunction
function automatic logic [USER_WIDTH-1:0] user_slice(input logic [M_COUNT*USER_WIDTH-1:0] bus, input int unsigned i);
    return bus[i*USER_WIDTH +: USER_WIDTH];
endfunction

// Basic protocol: input side must hold payload when stalled
assert property
( s_axis_tvalid && !s_axis_tready
  |-> s_axis_tvalid until_with (s_axis_tvalid && s_axis_tready)
      and $stable(s_axis_tdata)
      and (KEEP_ENABLE ? $stable(s_axis_tkeep) : 1)
      and (ID_ENABLE   ? $stable(s_axis_tid)   : 1)
      and (DEST_ENABLE ? $stable(s_axis_tdest) : 1)
      and (USER_ENABLE ? $stable(s_axis_tuser) : 1)
      and $stable(s_axis_tlast)
) else $error("AXIS input payload changed while not ready");

// s_axis_tready must be low when enable=0
assert property (!enable |-> !s_axis_tready) else $error("s_axis_tready high while enable=0");

// One-hot or zero on output valid
assert property ($onehot0(m_axis_tvalid)) else $error("m_axis_tvalid not onehot0");

// Output must hold selected payload until handshake on that output bit
genvar gi;
generate for (gi=0; gi<M_COUNT; gi++) begin: OUT_HOLD
    assert property
    ( m_axis_tvalid[gi] && !m_axis_tready[gi]
      |-> ( m_axis_tvalid[gi]
            and $stable(data_slice(m_axis_tdata, gi))
            and $stable(m_axis_tlast[gi])
            and (KEEP_ENABLE ? $stable(keep_slice(m_axis_tkeep, gi)) : 1)
            and (ID_ENABLE   ? $stable(id_slice(m_axis_tid, gi))     : 1)
            and (DEST_ENABLE ? $stable(dest_slice(m_axis_tdest, gi)) : 1)
            and (USER_ENABLE ? $stable(user_slice(m_axis_tuser, gi)) : 1)
          ) until_with (m_axis_tvalid[gi] && m_axis_tready[gi])
    ) else $error("Output %0d payload changed while stalled", gi);
end endgenerate

// Replication consistency across M outputs (all slices equal)
generate if (M_COUNT > 1) begin: REPL_EQ
    genvar rj;
    for (rj=1; rj<M_COUNT; rj++) begin: REPL
        assert property (data_slice(m_axis_tdata, rj) == data_slice(m_axis_tdata, 0))
            else $error("m_axis_tdata replication mismatch");
        assert property (m_axis_tlast[rj] == m_axis_tlast[0])
            else $error("m_axis_tlast replication mismatch");
        if (KEEP_ENABLE) begin
            assert property (keep_slice(m_axis_tkeep, rj) == keep_slice(m_axis_tkeep, 0))
                else $error("m_axis_tkeep replication mismatch");
        end
        if (ID_ENABLE) begin
            assert property (id_slice(m_axis_tid, rj) == id_slice(m_axis_tid, 0))
                else $error("m_axis_tid replication mismatch");
        end
        if (DEST_ENABLE) begin
            assert property (dest_slice(m_axis_tdest, rj) == dest_slice(m_axis_tdest, 0))
                else $error("m_axis_tdest replication mismatch");
        end
        if (USER_ENABLE) begin
            assert property (user_slice(m_axis_tuser, rj) == user_slice(m_axis_tuser, 0))
                else $error("m_axis_tuser replication mismatch");
        end
    end
end endgenerate

// Disabled fields forced constants on outputs
if (!KEEP_ENABLE) begin
    assert property (m_axis_tkeep == {M_COUNT*KEEP_WIDTH{1'b1}})
        else $error("KEEP disabled but m_axis_tkeep not all ones");
end
if (!ID_ENABLE && ID_WIDTH>0) begin
    assert property (m_axis_tid == '0)
        else $error("ID disabled but m_axis_tid not zero");
end
if (!DEST_ENABLE && DEST_WIDTH>0) begin
    assert property (m_axis_tdest == '0)
        else $error("DEST disabled but m_axis_tdest not zero");
end
if (!USER_ENABLE && USER_WIDTH>0) begin
    assert property (m_axis_tuser == '0)
        else $error("USER disabled but m_axis_tuser not zero");
end

// Forwarding correctness under ready (bounded latency if selected output stays ready)
// If a beat is accepted and not dropped, and the selected output remains ready
// for 3 cycles, it must be forwarded within 1..3 cycles with identical payload.
property fwd_if_ready_p;
    int unsigned sel;
    logic [DATA_WIDTH-1:0] d;
    logic [KEEP_WIDTH-1:0] k;
    logic [ID_WIDTH-1:0]   idv;
    logic [DEST_WIDTH-1:0] dv;
    logic [USER_WIDTH-1:0] uv;
    logic                   ls;
    (s_axis_tvalid && s_axis_tready && !drop)
    ##0 (sel = select, d = s_axis_tdata, k = s_axis_tkeep, idv = s_axis_tid, dv = s_axis_tdest, uv = s_axis_tuser, ls = s_axis_tlast, 1'b1)
    |-> (m_axis_tready[sel] [*3])
        |-> ##[1:3]
            ( m_axis_tvalid[sel] && m_axis_tready[sel]
              && data_slice(m_axis_tdata, sel) == d
              && m_axis_tlast[sel] == ls
              && (KEEP_ENABLE ? keep_slice(m_axis_tkeep, sel) == k : 1)
              && (ID_ENABLE   ? id_slice(m_axis_tid, sel)     == idv : 1)
              && (DEST_ENABLE ? dest_slice(m_axis_tdest, sel) == dv  : 1)
              && (USER_ENABLE ? user_slice(m_axis_tuser, sel) == uv  : 1)
            );
endproperty
assert property (fwd_if_ready_p) else $error("Forwarding under ready failed");

// Coverage

// Cover: handshake on each output
generate for (gi=0; gi<M_COUNT; gi++) begin: COV_PER_OUT
    cover property (m_axis_tvalid[gi] && m_axis_tready[gi]);
end endgenerate

// Cover: single-beat frame forwarded (tlast with acceptance and matching out)
cover property
( s_axis_tvalid && s_axis_tready && s_axis_tlast && !drop
  ##[1:3] m_axis_tvalid[select] && m_axis_tready[select] && m_axis_tlast[select]
);

// Cover: multi-beat frame (two accepts with last on second)
cover property
( s_axis_tvalid && s_axis_tready && !s_axis_tlast
  ##1 s_axis_tvalid && s_axis_tready && s_axis_tlast
);

// Cover: drop asserted on an accepted beat
cover property (s_axis_tvalid && s_axis_tready && drop);

// Cover: backpressure while new input accepted (temp path utilization scenario)
cover property
( (|m_axis_tvalid) && (|(m_axis_tvalid & ~m_axis_tready))
  && s_axis_tvalid && s_axis_tready && !drop
);

// Cover: change of select across frames (two accepted first beats with different select)
cover property
( s_axis_tvalid && s_axis_tready && s_axis_tlast ##1
  s_axis_tvalid && s_axis_tready && !drop ##0 1
  ##[1:10] s_axis_tvalid && s_axis_tready && !drop && (select != $past(select,1))
);

endmodule