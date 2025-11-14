// SVA for axis_variable
module axis_variable_sva #(
  parameter int AXIS_TDATA_WIDTH = 32
)(
  input  logic                        aclk,
  input  logic                        aresetn,
  input  logic [AXIS_TDATA_WIDTH-1:0] cfg_data,
  input  logic                        m_axis_tready,
  input  logic [AXIS_TDATA_WIDTH-1:0] m_axis_tdata,
  input  logic                        m_axis_tvalid
);

  default clocking cb @(posedge aclk); endclocking

  // Reset-state check (no disable)
  assert property (@(posedge aclk) !aresetn |-> (!m_axis_tvalid && m_axis_tdata == '0));

  // After reset deasserted
  default disable iff (!aresetn);

  // Data register captures cfg_data each cycle
  assert property ($past(aresetn) |-> m_axis_tdata == $past(cfg_data));

  // AXI-Stream stability: data must hold when VALID=1 and READY=0
  assert property (m_axis_tvalid && !m_axis_tready |-> $stable(m_axis_tdata));

  // VALID next-state function (handshake has precedence over change-detect)
  assert property (
    $past(aresetn) |->
    m_axis_tvalid == (
      (!($past(m_axis_tvalid) && $past(m_axis_tready))) &&
      ($past(m_axis_tvalid) || ($past(m_axis_tdata) != cfg_data))
    )
  );

  // Explicit handshake drop next cycle
  assert property ($past(m_axis_tvalid) && $past(m_axis_tready) |-> !m_axis_tvalid);

  // No spurious VALID when no change and not previously valid
  assert property (!$past(m_axis_tvalid) && ($past(m_axis_tdata) == cfg_data) |-> !m_axis_tvalid);

  // Coverage
  cover property ($past(aresetn) && ($past(m_axis_tdata) != cfg_data) ##1 m_axis_tvalid ##[1:$] (m_axis_tvalid && m_axis_tready) ##1 !m_axis_tvalid);
  cover property (m_axis_tvalid && !m_axis_tready [*3] ##1 (m_axis_tvalid && m_axis_tready));
  cover property ($rose(m_axis_tvalid) ##[1:8] (m_axis_tvalid && m_axis_tready) ##1 !m_axis_tvalid);

endmodule

// Bind into DUT
bind axis_variable axis_variable_sva #(.AXIS_TDATA_WIDTH(AXIS_TDATA_WIDTH)) u_axis_variable_sva (
  .aclk(aclk),
  .aresetn(aresetn),
  .cfg_data(cfg_data),
  .m_axis_tready(m_axis_tready),
  .m_axis_tdata(m_axis_tdata),
  .m_axis_tvalid(m_axis_tvalid)
);