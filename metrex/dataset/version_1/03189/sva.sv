// SVA for axi_write_controller
// Bind this module to the DUT instance (example at bottom).

module axi_write_controller_sva #(
  parameter M_AXI_TDATA_WIDTH = 32,
  parameter M_AXI_ADDR_WIDTH  = 32,
  parameter BAR0AXI           = 64'h0,
  parameter BAR1AXI           = 64'h0,
  parameter BAR2AXI           = 64'h0,
  parameter BAR3AXI           = 64'h0,
  parameter BAR4AXI           = 64'h0,
  parameter BAR5AXI           = 64'h0,
  parameter BAR0SIZE          = 12,
  parameter BAR1SIZE          = 12,
  parameter BAR2SIZE          = 12,
  parameter BAR3SIZE          = 12,
  parameter BAR4SIZE          = 12,
  parameter BAR5SIZE          = 12
)(
  input                           m_axi_aclk,
  input                           m_axi_aresetn,

  input       [M_AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
  input       [2:0]               m_axi_awprot,
  input                           m_axi_awvalid,
  input                           m_axi_awready,

  input       [M_AXI_TDATA_WIDTH-1:0]   m_axi_wdata,
  input       [M_AXI_TDATA_WIDTH/8-1:0] m_axi_wstrb,
  input                           m_axi_wvalid,
  input                           m_axi_wready,

  input       [1:0]               m_axi_bresp,
  input                           m_axi_bvalid,
  input                           m_axi_bready,

  input                           mem_req_valid,
  input                           mem_req_ready,
  input       [2:0]               mem_req_bar_hit,
  input       [31:0]              mem_req_pcie_address,
  input       [3:0]               mem_req_byte_enable,
  input                           mem_req_write_readn,
  input                           mem_req_phys_func,
  input       [31:0]              mem_req_write_data
);

  default clocking cb @ (posedge m_axi_aclk); endclocking
  default disable iff (!m_axi_aresetn);

  // Helper: expected AW address mapping for the accepted request
  function automatic [M_AXI_ADDR_WIDTH-1:0]
    f_expected_awaddr (input [2:0] bar, input [31:0] pa);
    case (bar)
      3'b000: f_expected_awaddr = { BAR0AXI[M_AXI_ADDR_WIDTH-1:BAR0SIZE], pa[BAR0SIZE-1:2], 2'b00 };
      3'b001: f_expected_awaddr = { BAR1AXI[M_AXI_ADDR_WIDTH-1:BAR1SIZE], pa[BAR1SIZE-1:2], 2'b00 };
      3'b010: f_expected_awaddr = { BAR2AXI[M_AXI_ADDR_WIDTH-1:BAR2SIZE], pa[BAR2SIZE-1:2], 2'b00 };
      3'b011: f_expected_awaddr = { BAR3AXI[M_AXI_ADDR_WIDTH-1:BAR3SIZE], pa[BAR3SIZE-1:2], 2'b00 };
      3'b100: f_expected_awaddr = { BAR4AXI[M_AXI_ADDR_WIDTH-1:BAR4SIZE], pa[BAR4SIZE-1:2], 2'b00 };
      3'b101: f_expected_awaddr = { BAR5AXI[M_AXI_ADDR_WIDTH-1:BAR5SIZE], pa[BAR5SIZE-1:2], 2'b00 };
      default: f_expected_awaddr = '0;
    endcase
  endfunction

  // AXI protocol essentials
  assert property (m_axi_awprot == 3'b000);
  assert property (m_axi_awvalid && !m_axi_awready |=> m_axi_awvalid);
  assert property (m_axi_wvalid  && !m_axi_wready  |=> m_axi_wvalid);

  assert property (m_axi_awvalid && !m_axi_awready |=> $stable(m_axi_awaddr));
  assert property (m_axi_wvalid  && !m_axi_wready  |=> $stable(m_axi_wdata) && $stable(m_axi_wstrb));

  // No overlapping AW and W channels for this simple controller
  assert property (!(m_axi_awvalid && m_axi_wvalid));

  // Write data can only start after or with AW handshake
  assert property ($rose(m_axi_wvalid) |-> (m_axi_awvalid && m_axi_awready) || $past(m_axi_awvalid && m_axi_awready));

  // Address alignment
  assert property (m_axi_awvalid |-> m_axi_awaddr[1:0] == 2'b00);

  // Backpressure to requestor while transaction in-flight
  assert property (m_axi_awvalid |-> !mem_req_ready);
  assert property (m_axi_wvalid  |-> !mem_req_ready);

  // AWVALID only starts due to an accepted WRITE request
  assert property ($rose(m_axi_awvalid) |-> $past(mem_req_valid && mem_req_ready && mem_req_write_readn));

  // When AWVALID rises, address equals mapped BAR/PCIE address of accepted request
  assert property ($rose(m_axi_awvalid)
                   |-> m_axi_awaddr == f_expected_awaddr($past(mem_req_bar_hit), $past(mem_req_pcie_address)));

  // Write data/strb correspond to accepted request when WVALID rises
  // (single outstanding write ensures these are from the last acceptance)
  assert property ($rose(m_axi_wvalid)
                   |-> m_axi_wdata == $past(mem_req_write_data, 1) or
                       m_axi_wdata == $past(mem_req_write_data, 2) or
                       m_axi_wdata == $past(mem_req_write_data, 3)); // small window tolerance
  assert property ($rose(m_axi_wvalid)
                   |-> m_axi_wstrb == $past(mem_req_byte_enable, 1) or
                       m_axi_wstrb == $past(mem_req_byte_enable, 2) or
                       m_axi_wstrb == $past(mem_req_byte_enable, 3));

  // B channel is always ready
  assert property (m_axi_bready);

  // ------------------
  // Coverage
  // ------------------
  sequence s_accept; mem_req_valid && mem_req_ready && mem_req_write_readn; endsequence
  sequence s_aw_hs;  m_axi_awvalid && m_axi_awready; endsequence
  sequence s_w_hs;   m_axi_wvalid  && m_axi_wready; endsequence

  // Full write path
  cover property (s_accept ##[0:5] s_aw_hs ##[0:10] s_w_hs);

  // Stall scenarios
  cover property (m_axi_awvalid && !m_axi_awready ##1 m_axi_awvalid && m_axi_awready);
  cover property (m_axi_wvalid  && !m_axi_wready  ##1 m_axi_wvalid  && m_axi_wready);

  // BAR hit coverage (on write start)
  cover property ($rose(m_axi_awvalid) && $past(mem_req_bar_hit)==3'b000);
  cover property ($rose(m_axi_awvalid) && $past(mem_req_bar_hit)==3'b001);
  cover property ($rose(m_axi_awvalid) && $past(mem_req_bar_hit)==3'b010);
  cover property ($rose(m_axi_awvalid) && $past(mem_req_bar_hit)==3'b011);
  cover property ($rose(m_axi_awvalid) && $past(mem_req_bar_hit)==3'b100);
  cover property ($rose(m_axi_awvalid) && $past(mem_req_bar_hit)==3'b101);
  cover property ($rose(m_axi_awvalid) && $past(mem_req_bar_hit)==3'b110);
  cover property ($rose(m_axi_awvalid) && $past(mem_req_bar_hit)==3'b111);

endmodule

// Example bind (adjust instance/path/parameters as needed):
// bind axi_write_controller axi_write_controller_sva #(
//   .M_AXI_TDATA_WIDTH(M_AXI_TDATA_WIDTH),
//   .M_AXI_ADDR_WIDTH (M_AXI_ADDR_WIDTH),
//   .BAR0AXI(BAR0AXI), .BAR1AXI(BAR1AXI), .BAR2AXI(BAR2AXI),
//   .BAR3AXI(BAR3AXI), .BAR4AXI(BAR4AXI), .BAR5AXI(BAR5AXI),
//   .BAR0SIZE(BAR0SIZE), .BAR1SIZE(BAR1SIZE), .BAR2SIZE(BAR2SIZE),
//   .BAR3SIZE(BAR3SIZE), .BAR4SIZE(BAR4SIZE), .BAR5SIZE(BAR5SIZE)
// ) i_sva (.*);