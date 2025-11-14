// SVA checker for ptp_tag_insert
module ptp_tag_insert_sva #(
    parameter DATA_WIDTH = 64,
    parameter KEEP_WIDTH = DATA_WIDTH/8,
    parameter TAG_WIDTH  = 16,
    parameter TAG_OFFSET = 1,
    parameter USER_WIDTH = TAG_WIDTH+TAG_OFFSET
)(
    input  wire                   clk,
    input  wire                   rst,

    input  wire [DATA_WIDTH-1:0]  s_axis_tdata,
    input  wire [KEEP_WIDTH-1:0]  s_axis_tkeep,
    input  wire                   s_axis_tvalid,
    input  wire                   s_axis_tready,
    input  wire                   s_axis_tlast,
    input  wire [USER_WIDTH-1:0]  s_axis_tuser,

    input  wire [DATA_WIDTH-1:0]  m_axis_tdata,
    input  wire [KEEP_WIDTH-1:0]  m_axis_tkeep,
    input  wire                   m_axis_tvalid,
    input  wire                   m_axis_tready,
    input  wire                   m_axis_tlast,
    input  wire [USER_WIDTH-1:0]  m_axis_tuser,

    input  wire [TAG_WIDTH-1:0]   s_axis_tag,
    input  wire                   s_axis_tag_valid,
    input  wire                   s_axis_tag_ready
);

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

// Parameter/slice sanity
initial begin
    assert (TAG_OFFSET+TAG_WIDTH <= USER_WIDTH)
        else $error("TAG slice exceeds USER_WIDTH");
end

// Sample the tag value when accepted (ready & valid high)
logic [TAG_WIDTH-1:0] tag_latched;
always_ff @(posedge clk) if (!rst && s_axis_tag_ready && s_axis_tag_valid) tag_latched <= s_axis_tag;

// Basic pass-through and gating relations
assert property (m_axis_tdata  == s_axis_tdata);
assert property (m_axis_tkeep  == s_axis_tkeep);
assert property (m_axis_tlast  == s_axis_tlast);

// Ready/valid gating by tag presence: tag_present = !s_axis_tag_ready
assert property (s_axis_tready == (m_axis_tready && !s_axis_tag_ready));
assert property (m_axis_tvalid == (s_axis_tvalid && !s_axis_tag_ready));
assert property ((m_axis_tvalid && m_axis_tready) == (s_axis_tvalid && s_axis_tready));

// Tag lifecycle using tag_ready (= !tag_valid_reg)
// New tag is latched only when tag_ready && tag_valid, and tag_ready must fall next cycle
assert property ($fell(s_axis_tag_ready) |-> $past(s_axis_tag_ready && s_axis_tag_valid));

// tag_ready rises only after completing a beat with tlast
assert property ($rose(s_axis_tag_ready) |-> $past(s_axis_tvalid && s_axis_tready && s_axis_tlast));

// While a tag is active, it remains active until the last beat handshake
assert property (!s_axis_tag_ready && !(s_axis_tvalid && s_axis_tready && s_axis_tlast) |=> !s_axis_tag_ready);

// USER field composition
// Inserted slice equals the latched tag whenever output is valid
assert property (m_axis_tvalid |-> m_axis_tuser[TAG_OFFSET +: TAG_WIDTH] == tag_latched);

// Outside the inserted slice, USER passes through unmodified
if (TAG_OFFSET > 0) begin
    assert property (m_axis_tuser[TAG_OFFSET-1:0] == s_axis_tuser[TAG_OFFSET-1:0]);
end
if (USER_WIDTH > TAG_OFFSET+TAG_WIDTH) begin
    assert property (m_axis_tuser[USER_WIDTH-1:TAG_OFFSET+TAG_WIDTH] ==
                     s_axis_tuser[USER_WIDTH-1:TAG_OFFSET+TAG_WIDTH]);
end

// Reset behavior: after deasserting rst, tag_ready must be high (no tag active)
assert property ($fell(rst) |=> s_axis_tag_ready);

// Coverage
// Accept a tag, send multi-beat frame, then release tag
cover property (s_axis_tag_ready && s_axis_tag_valid ##1
                !s_axis_tag_ready ##[1:5]
                (s_axis_tvalid && s_axis_tready && !s_axis_tlast) ##1
                (s_axis_tvalid && s_axis_tready &&  s_axis_tlast) ##1
                s_axis_tag_ready);

// Single-beat frame
cover property (s_axis_tag_ready && s_axis_tag_valid ##1
                !s_axis_tag_ready ##1
                (s_axis_tvalid && s_axis_tready && s_axis_tlast) ##1
                s_axis_tag_ready);

// Back-to-back frames with back-to-back tags
cover property (s_axis_tag_ready && s_axis_tag_valid ##1
                !s_axis_tag_ready ##[1:5]
                (s_axis_tvalid && s_axis_tready && s_axis_tlast) ##1
                s_axis_tag_valid ##1
                !s_axis_tag_ready);

// Stall scenario: data present but blocked until tag available
cover property (s_axis_tvalid && s_axis_tag_ready && !m_axis_tvalid);
endmodule

// Bind example:
// bind ptp_tag_insert ptp_tag_insert_sva #(
//   .DATA_WIDTH(DATA_WIDTH), .KEEP_WIDTH(KEEP_WIDTH),
//   .TAG_WIDTH(TAG_WIDTH), .TAG_OFFSET(TAG_OFFSET), .USER_WIDTH(USER_WIDTH)
// ) ptp_tag_insert_sva_i (.*);