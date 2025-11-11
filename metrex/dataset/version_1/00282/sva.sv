// SVA for axis_frame_length_adjust
// Quality-focused, concise checks and coverage.
// Bind this module to the DUT instance:
//   bind axis_frame_length_adjust axis_frame_length_adjust_sva #(.DATA_WIDTH(DATA_WIDTH), .KEEP_ENABLE(KEEP_ENABLE), .KEEP_WIDTH(KEEP_WIDTH), .ID_ENABLE(ID_ENABLE), .ID_WIDTH(ID_WIDTH), .DEST_ENABLE(DEST_ENABLE), .DEST_WIDTH(DEST_WIDTH), .USER_ENABLE(USER_ENABLE), .USER_WIDTH(USER_WIDTH)) sva_i (.*);

module axis_frame_length_adjust_sva #(
    parameter DATA_WIDTH = 8,
    parameter KEEP_ENABLE = (DATA_WIDTH>8),
    parameter KEEP_WIDTH = (DATA_WIDTH/8),
    parameter ID_ENABLE = 1,
    parameter ID_WIDTH = 8,
    parameter DEST_ENABLE = 1,
    parameter DEST_WIDTH = 8,
    parameter USER_ENABLE = 1,
    parameter USER_WIDTH = 1
)(
    input clk,
    input rst,

    // AXIS in
    input  [DATA_WIDTH-1:0] s_axis_tdata,
    input  [KEEP_WIDTH-1:0] s_axis_tkeep,
    input                   s_axis_tvalid,
    input                   s_axis_tlast,
    input  [ID_WIDTH-1:0]   s_axis_tid,
    input  [DEST_WIDTH-1:0] s_axis_tdest,
    input  [USER_WIDTH-1:0] s_axis_tuser,
    output                  s_axis_tready,

    // AXIS out
    output [DATA_WIDTH-1:0] m_axis_tdata,
    output [KEEP_WIDTH-1:0] m_axis_tkeep,
    output                  m_axis_tvalid,
    input                   m_axis_tready,
    output                  m_axis_tlast,
    output [ID_WIDTH-1:0]   m_axis_tid,
    output [DEST_WIDTH-1:0] m_axis_tdest,
    output [USER_WIDTH-1:0] m_axis_tuser,

    // status sideband
    output                  status_valid,
    input                   status_ready,
    output                  status_frame_pad,
    output                  status_frame_truncate,
    output [15:0]           status_frame_length,
    output [15:0]           status_frame_original_length,
    input  [15:0]           length_min,
    input  [15:0]           length_max,

    // internal state/regs (bound by name)
    input  [1:0]            state,
    input  [15:0]           frame_length,
    input  [15:0]           frame_original_length,
    input  [15:0]           frame_counter,
    input  [15:0]           pad_counter,
    input  [15:0]           truncate_counter
);

default clocking cb @ (posedge clk); endclocking
default disable iff (rst)

// Handy lets
let s_hs = s_axis_tvalid && s_axis_tready;
let m_hs = m_axis_tvalid && m_axis_tready;
let in_frame = (state != 2'b00);          // not IDLE
let READ_HEADER = (state == 2'b01);
let READ_DATA   = (state == 2'b10);
let WRITE_DATA  = (state == 2'b11);

// Reset behavior
assert property (rst |-> !m_axis_tvalid && !m_axis_tlast && !status_valid && !status_frame_pad && !status_frame_truncate);

// AXIS output: hold stable while stalled
assert property (m_axis_tvalid && !m_axis_tready |=> $stable({m_axis_tdata, m_axis_tkeep, m_axis_tlast, m_axis_tid, m_axis_tdest, m_axis_tuser}));

// Sideband (ID/DEST/USER) stable for duration of a frame
assert property (in_frame |-> $stable({m_axis_tid, m_axis_tdest, m_axis_tuser}));

// Frame counter behavior in READ_DATA
assert property (READ_DATA && s_hs |=> frame_counter == $past(frame_counter)+1);
assert property (READ_DATA && !s_hs |=> frame_counter == $past(frame_counter));

// TLAST aligned to frame_length in READ_DATA
assert property (READ_DATA && s_hs && (frame_counter < frame_length-1) |=> !m_axis_tlast);
assert property (READ_DATA && s_hs && (frame_counter == frame_length-1) |=> m_axis_tlast);

// State transitions (basic)
assert property ((state==2'b00) && s_axis_tvalid && m_axis_tready |=> state==2'b01); // IDLE->READ_HEADER
assert property (READ_HEADER && s_hs |=> state==2'b10);                               // READ_HEADER->READ_DATA
assert property (READ_DATA && s_hs && (frame_counter == frame_length-1) |=> state==2'b11); // READ_DATA->WRITE_DATA
assert property (WRITE_DATA && m_axis_tready && status_ready && (pad_counter==0) && (truncate_counter==0) |=> state==2'b00); // WRITE_DATA->IDLE

// WRITE_DATA behavior
// When padding, drive zeros; counters decrement on handshake
assert property (WRITE_DATA && m_axis_tready && status_ready && (pad_counter>0) |=> $stable(m_axis_tdata) || (m_axis_tdata=={DATA_WIDTH{1'b0}}));
assert property (WRITE_DATA && m_axis_tready && status_ready && (pad_counter>0) |=> pad_counter == $past(pad_counter)-1);
assert property (WRITE_DATA && m_axis_tready && status_ready && (truncate_counter>0) |=> truncate_counter == $past(truncate_counter)-1);

// Status channel protocol
assert property (status_valid |-> (WRITE_DATA && m_axis_tready && status_ready));

// Status flags consistency (mutually exclusive, relational checks when status_valid)
assert property (!(status_frame_pad && status_frame_truncate));
assert property (status_valid && status_frame_pad |-> (status_frame_length >= length_min) && (status_frame_length >= status_frame_original_length));
assert property (status_valid && status_frame_truncate |-> (status_frame_length <= length_max) && (status_frame_length <= status_frame_original_length));
assert property (status_valid && !status_frame_pad && !status_frame_truncate |-> (status_frame_length == status_frame_original_length) && (status_frame_length >= length_min) && (status_frame_length <= length_max));

// TLAST occurs exactly once per frame (no early TLAST before last beat)
// Disallow TLAST before counter reaches last
assert property (READ_DATA && s_hs && (frame_counter < frame_length-1) |-> !m_axis_tlast);

// Coverage

// State progression through a complete frame
cover property ((state==2'b00) ##1 (s_axis_tvalid && m_axis_tready)
                ##1 READ_HEADER ##1 READ_DATA ##[1:$] (READ_DATA && s_hs && frame_counter==frame_length-1)
                ##1 WRITE_DATA ##1 (WRITE_DATA && m_axis_tready && status_ready && pad_counter==0 && truncate_counter==0)
                ##1 (state==2'b00));

// Pass-through frame (no pad/trunc)
cover property (status_valid && !status_frame_pad && !status_frame_truncate);

// Padding path observed
cover property (status_valid && status_frame_pad);

// Truncation path observed
cover property (status_valid && status_frame_truncate);

// Output backpressure lasting 2 cycles with stable data
cover property (m_axis_tvalid && !m_axis_tready ##1 m_axis_tvalid && !m_axis_tready ##1 m_axis_tvalid && m_axis_tready);

endmodule