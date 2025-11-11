Here’s a concise, bindable SVA checker that fully covers and verifies the key behaviors of axis_lfsr. It focuses on reset behavior, valid monotonicity, handshake-driven LFSR update, and data stability under backpressure. It assumes the intended 64-bit configuration used by the RTL.

module axis_lfsr_chk #(
  parameter int AXIS_TDATA_WIDTH = 64
)(
  input  logic                        aclk,
  input  logic                        aresetn,
  input  logic                        m_axis_tready,
  input  logic [AXIS_TDATA_WIDTH-1:0] m_axis_tdata,
  input  logic                        m_axis_tvalid
);

  // Static design sanity
  initial begin
    if (AXIS_TDATA_WIDTH != 64) $error("axis_lfsr: AXIS_TDATA_WIDTH must be 64");
  end

  // Default clocking
  default clocking cb @(posedge aclk); endclocking

  // During reset, outputs are forced to seed and valid=0
  assert property (@cb !aresetn |-> (m_axis_tvalid==1'b0 && m_axis_tdata==64'h5555_5555_5555_5555));

  // Valid goes high on reset release and never drops except in reset
  assert property (@cb $rose(aresetn) |-> m_axis_tvalid);
  assert property (@cb disable iff (!aresetn) m_axis_tvalid |=> m_axis_tvalid);
  assert property (@cb $fell(m_axis_tvalid) |-> !aresetn);

  // No X/Z on outputs after reset
  assert property (@cb disable iff (!aresetn) !$isunknown({m_axis_tvalid, m_axis_tdata}));

  // LFSR update only on handshake; otherwise data holds
  // Next state: {prev[62:0], prev[62] ~^ prev[61]} when valid&&ready
  assert property (@cb disable iff (!aresetn)
    $past(m_axis_tvalid && m_axis_tready)
    |-> m_axis_tdata == { $past(m_axis_tdata[62:0]), ($past(m_axis_tdata[62]) ~^ $past(m_axis_tdata[61])) }
  );

  assert property (@cb disable iff (!aresetn)
    !$past(m_axis_tvalid && m_axis_tready)
    |-> m_axis_tdata == $past(m_axis_tdata)
  );

  // Coverage
  // 1) Reset release followed by first handshake (and an update)
  cover property (@cb $rose(aresetn) ##1 (m_axis_tvalid && m_axis_tready)
                      ##1 (m_axis_tdata != $past(m_axis_tdata)));

  // 2) Backpressure: valid high, ready low for a few cycles, then handshake
  cover property (@cb disable iff (!aresetn)
    m_axis_tvalid && !m_axis_tready [*3] ##1 (m_axis_tvalid && m_axis_tready));

  // 3) Feedback bit exercises both 0 and 1 on some handshakes
  cover property (@cb disable iff (!aresetn)
    $past(m_axis_tvalid && m_axis_tready) && (($past(m_axis_tdata[62]) ~^ $past(m_axis_tdata[61])) == 1'b0));
  cover property (@cb disable iff (!aresetn)
    $past(m_axis_tvalid && m_axis_tready) && (($past(m_axis_tdata[62]) ~^ $past(m_axis_tdata[61])) == 1'b1));

endmodule

// Bind into the DUT (instance-agnostic)
bind axis_lfsr axis_lfsr_chk #(.AXIS_TDATA_WIDTH(AXIS_TDATA_WIDTH)) i_axis_lfsr_chk (
  .aclk(aclk),
  .aresetn(aresetn),
  .m_axis_tready(m_axis_tready),
  .m_axis_tdata(m_axis_tdata),
  .m_axis_tvalid(m_axis_tvalid)
);