// SVA for axis_srl_fifo
// Bind this module to the DUT instance(s).
// Focus: handshake correctness, flags/pointer consistency, stability on backpressure, FWFT behavior, bounds, and useful coverage.

`ifndef AXIS_SRL_FIFO_SVA_SV
`define AXIS_SRL_FIFO_SVA_SV

module axis_srl_fifo_sva #(
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter LAST_ENABLE = 1,
    parameter ID_ENABLE = 0,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 0,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1,
    parameter DEPTH = 16
)(
    input  logic                       clk,
    input  logic                       rst,

    // AXIS in
    input  logic [DATA_WIDTH-1:0]      s_axis_tdata,
    input  logic [KEEP_WIDTH-1:0]      s_axis_tkeep,
    input  logic                       s_axis_tvalid,
    input  logic                       s_axis_tready,
    input  logic                       s_axis_tlast,
    input  logic [ID_WIDTH-1:0]        s_axis_tid,
    input  logic [DEST_WIDTH-1:0]      s_axis_tdest,
    input  logic [USER_WIDTH-1:0]      s_axis_tuser,

    // AXIS out
    input  logic [DATA_WIDTH-1:0]      m_axis_tdata,
    input  logic [KEEP_WIDTH-1:0]      m_axis_tkeep,
    input  logic                       m_axis_tvalid,
    input  logic                       m_axis_tready,
    input  logic                       m_axis_tlast,
    input  logic [ID_WIDTH-1:0]        m_axis_tid,
    input  logic [DEST_WIDTH-1:0]      m_axis_tdest,
    input  logic [USER_WIDTH-1:0]      m_axis_tuser,

    input  logic [$clog2(DEPTH+1)-1:0] count,

    // Internal state (bind to DUT internals)
    input  logic [$clog2(DEPTH+1)-1:0] ptr_reg,
    input  logic                       full_reg,
    input  logic                       empty_reg,
    input  logic                       shift
);

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

logic s_fire, m_fire;
assign s_fire = s_axis_tvalid && s_axis_tready;
assign m_fire = m_axis_tvalid && m_axis_tready;

// Reset state
assert property (rst |-> (ptr_reg==0 && empty_reg && !full_reg && count==0 && !m_axis_tvalid));

// Basic equivalences
assert property (s_axis_tready == !full_reg);
assert property (m_axis_tvalid == !empty_reg);
assert property (count == ptr_reg);

// Bounds and flags
assert property (ptr_reg <= DEPTH);
assert property ((ptr_reg==0) <-> empty_reg);
assert property ((ptr_reg==DEPTH) <-> full_reg);

// Conservation of elements
assert property (ptr_reg == $past(ptr_reg)
                 + ($past(s_axis_tvalid && s_axis_tready) ? 1 : 0)
                 - ($past(m_axis_tvalid && m_axis_tready) ? 1 : 0));

// No activity => stable count
assert property (!s_fire && !m_fire |-> ptr_reg == $past(ptr_reg));

// No underflow on read
assert property (m_fire |-> $past(ptr_reg) > 0);

// Backpressure: hold payload and valid
assert property (m_axis_tvalid && !m_axis_tready |-> $stable(m_axis_tvalid));
assert property (m_axis_tvalid && !m_axis_tready |-> $stable(m_axis_tdata));
assert property (m_axis_tvalid && !m_axis_tready |-> $stable(m_axis_tkeep));
assert property (m_axis_tvalid && !m_axis_tready |-> $stable(m_axis_tlast));
assert property (m_axis_tvalid && !m_axis_tready |-> $stable(m_axis_tid));
assert property (m_axis_tvalid && !m_axis_tready |-> $stable(m_axis_tdest));
assert property (m_axis_tvalid && !m_axis_tready |-> $stable(m_axis_tuser));

// Shift happens iff write handshake
assert property (shift == s_fire);

// First-word fall-through on empty write
assert property ($past(ptr_reg)==0 && $past(s_axis_tvalid && s_axis_tready) |-> m_axis_tvalid);

// FWFT payload equivalence on empty->write
assert property ($past(ptr_reg)==0 && $past(s_axis_tvalid && s_axis_tready) |->
    (m_axis_tdata == $past(s_axis_tdata)));
if (KEEP_ENABLE)
    assert property ($past(ptr_reg)==0 && $past(s_axis_tvalid && s_axis_tready) |->
        (m_axis_tkeep == $past(s_axis_tkeep)));
else
    assert property (m_axis_tkeep == {KEEP_WIDTH{1'b1}});
if (LAST_ENABLE)
    assert property ($past(ptr_reg)==0 && $past(s_axis_tvalid && s_axis_tready) |->
        (m_axis_tlast == $past(s_axis_tlast)));
else
    assert property (m_axis_tlast == 1'b1);
if (ID_ENABLE)
    assert property ($past(ptr_reg)==0 && $past(s_axis_tvalid && s_axis_tready) |->
        (m_axis_tid == $past(s_axis_tid)));
else
    assert property (m_axis_tid == {ID_WIDTH{1'b0}});
if (DEST_ENABLE)
    assert property ($past(ptr_reg)==0 && $past(s_axis_tvalid && s_axis_tready) |->
        (m_axis_tdest == $past(s_axis_tdest)));
else
    assert property (m_axis_tdest == {DEST_WIDTH{1'b0}});
if (USER_ENABLE)
    assert property ($past(ptr_reg)==0 && $past(s_axis_tvalid && s_axis_tready) |->
        (m_axis_tuser == $past(s_axis_tuser)));
else
    assert property (m_axis_tuser == {USER_WIDTH{1'b0}});

// Simultaneous R/W when non-empty keeps count and remains valid
assert property (ptr_reg>0 && s_axis_tvalid && s_axis_tready && m_axis_tvalid && m_axis_tready |-> $stable(ptr_reg) && $past(m_axis_tvalid));

// Coverage
cover property (ptr_reg==0 ##1 s_fire ##[1:$] ptr_reg==DEPTH);
cover property (ptr_reg==DEPTH ##1 m_fire ##[1:$] ptr_reg==0);
cover property (m_axis_tvalid && !m_axis_tready ##1 m_axis_tvalid && !m_axis_tready);
cover property (ptr_reg>0 && s_axis_tvalid && s_axis_tready && m_axis_tvalid && m_axis_tready); // simultaneous R/W (non-empty)

endmodule

// Example bind (adjust instance path as needed)
// bind axis_srl_fifo axis_srl_fifo_sva #(
//   .DATA_WIDTH(DATA_WIDTH), .KEEP_ENABLE(KEEP_ENABLE), .KEEP_WIDTH(KEEP_WIDTH),
//   .LAST_ENABLE(LAST_ENABLE), .ID_ENABLE(ID_ENABLE), .ID_WIDTH(ID_WIDTH),
//   .DEST_ENABLE(DEST_ENABLE), .DEST_WIDTH(DEST_WIDTH), .USER_ENABLE(USER_ENABLE), .USER_WIDTH(USER_WIDTH),
//   .DEPTH(DEPTH)
// ) sva (.*); // If .* not allowed by your tool for internals, connect ports explicitly to DUT signals.

`endif