// SVA for axis_adder. Bind this module to the DUT instance.
// Example:
// bind axis_adder axis_adder_sva #(.AXIS_TDATA_WIDTH(AXIS_TDATA_WIDTH),
//                                  .AXIS_TDATA_SIGNED(AXIS_TDATA_SIGNED)) sva (.*);

module axis_adder_sva #(
  parameter int    AXIS_TDATA_WIDTH  = 32,
  parameter string AXIS_TDATA_SIGNED = "FALSE"
)(
  input  logic                        aclk,

  // DUT ports (directions irrelevant for bind)
  input  logic                        s_axis_a_tready,
  input  logic [AXIS_TDATA_WIDTH-1:0] s_axis_a_tdata,
  input  logic                        s_axis_a_tvalid,

  input  logic                        s_axis_b_tready,
  input  logic [AXIS_TDATA_WIDTH-1:0] s_axis_b_tdata,
  input  logic                        s_axis_b_tvalid,

  input  logic                        m_axis_tready,
  input  logic [AXIS_TDATA_WIDTH-1:0] m_axis_tdata,
  input  logic                        m_axis_tvalid
);

  default clocking cb @(posedge aclk); endclocking

  localparam bit SIGNED_MODE = (AXIS_TDATA_SIGNED == "TRUE");

  function automatic logic [AXIS_TDATA_WIDTH-1:0]
    exp_sum (input logic [AXIS_TDATA_WIDTH-1:0] a, b);
    if (SIGNED_MODE)
      exp_sum = $signed(a) + $signed(b);
    else
      exp_sum = a + b;
  endfunction

  // Handshake events
  sequence s_hs; s_axis_a_tvalid && s_axis_b_tvalid && s_axis_a_tready && s_axis_b_tready; endsequence
  sequence m_hs; m_axis_tvalid && m_axis_tready; endsequence

  // Ready/valid combinational relationships
  assert property (m_axis_tvalid == (s_axis_a_tvalid && s_axis_b_tvalid))
    else $error("m_axis_tvalid must be AND of s_axis_a_tvalid and s_axis_b_tvalid");

  assert property (s_axis_a_tready == (m_axis_tready && s_axis_a_tvalid && s_axis_b_tvalid))
    else $error("s_axis_a_tready must be m_ready & both s_valid");

  assert property (s_axis_b_tready == s_axis_a_tready)
    else $error("s_axis_b_tready must equal s_axis_a_tready");

  // Handshake equivalence: a/b transfers occur iff m transfer occurs (same cycle)
  assert property (s_hs <-> m_hs)
    else $error("Source and sink handshakes must be equivalent");

  // If both inputs valid but m not ready, no source ready is asserted
  assert property ((s_axis_a_tvalid && s_axis_b_tvalid && !m_axis_tready) |-> (!s_axis_a_tready && !s_axis_b_tready))
    else $error("When both s_valid and !m_ready, s_ready must be deasserted");

  // If only one input is valid, no ready and no m_valid
  assert property ((s_axis_a_tvalid ^ s_axis_b_tvalid) |-> (!s_axis_a_tready && !s_axis_b_tready && !m_axis_tvalid))
    else $error("Single-source valid must not drive ready or m_valid");

  // Data correctness
  assert property (m_axis_tvalid |-> (m_axis_tdata == exp_sum(s_axis_a_tdata, s_axis_b_tdata)))
    else $error("m_axis_tdata must equal a+b when m_valid");

  // AXI-Stream stability on sink: when holding valid without ready, data must be stable
  assert property ((m_axis_tvalid && !m_axis_tready) |-> $stable(m_axis_tdata))
    else $error("m_axis_tdata must be stable when m_valid && !m_ready");

`ifdef FORMAL
  // Optional environment assumptions for AXI-Stream source stability
  assume property ((s_axis_a_tvalid && !s_axis_a_tready) |-> $stable(s_axis_a_tdata));
  assume property ((s_axis_b_tvalid && !s_axis_b_tready) |-> $stable(s_axis_b_tdata));
`endif

  // Functional coverage
  cover property (m_hs); // Any successful transfer

  // Backpressure then release
  cover property (s_axis_a_tvalid && s_axis_b_tvalid && !m_axis_tready ##1
                  s_axis_a_tvalid && s_axis_b_tvalid && m_axis_tready ##1 m_hs);

  // Only one side valid observed
  cover property ((s_axis_a_tvalid ^ s_axis_b_tvalid) && !s_axis_a_tready && !s_axis_b_tready);

  // Corner-case arithmetic coverage
  if (!SIGNED_MODE) begin
    // Unsigned carry out (sum wraps below one operand)
    cover property (m_hs && (m_axis_tdata < s_axis_a_tdata));
    cover property (m_hs && (m_axis_tdata < s_axis_b_tdata));
    // Zero + Zero
    cover property (m_hs && (s_axis_a_tdata == '0) && (s_axis_b_tdata == '0));
    // Max + 1 wrap
    cover property (m_hs && (s_axis_a_tdata == {AXIS_TDATA_WIDTH{1'b1}}) && (s_axis_b_tdata == 'd1));
  end else begin
    // Signed overflow: same-sign operands, result sign differs
    cover property (m_hs &&
                    (($signed(s_axis_a_tdata) >= 0 && $signed(s_axis_b_tdata) >= 0 && $signed(m_axis_tdata) < 0) ||
                     ($signed(s_axis_a_tdata) <  0 && $signed(s_axis_b_tdata) <  0 && $signed(m_axis_tdata) >= 0)));
    // Negative + Positive, Positive + Negative
    cover property (m_hs && ($signed(s_axis_a_tdata) < 0)  && ($signed(s_axis_b_tdata) >= 0));
    cover property (m_hs && ($signed(s_axis_a_tdata) >= 0) && ($signed(s_axis_b_tdata) <  0));
    // Min + (-1), Max + 1
    cover property (m_hs && (s_axis_a_tdata[AXIS_TDATA_WIDTH-1] == 1'b1) && (s_axis_b_tdata == '1)); // -1
    cover property (m_hs && (s_axis_a_tdata == {1'b0,{(AXIS_TDATA_WIDTH-1){1'b1}}}) && (s_axis_b_tdata == 'd1));
  end

endmodule