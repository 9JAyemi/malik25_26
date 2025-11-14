// SVA for axi_dwidth_converter_v2_1_8_axi4lite_upsizer
// Focused, high-quality checks and essential coverage.
// Bind this file to the DUT.

module axi_dwidth_converter_v2_1_8_axi4lite_upsizer_sva #(
  parameter integer C_AXI_ADDR_WIDTH = 32,
  parameter integer C_AXI_SUPPORTS_WRITE = 1,
  parameter integer C_AXI_SUPPORTS_READ  = 1
)(
  input  logic                          aclk,
  input  logic                          aresetn,

  // Slave side
  input  logic [C_AXI_ADDR_WIDTH-1:0]   s_axi_awaddr,
  input  logic [2:0]                    s_axi_awprot,
  input  logic                          s_axi_awvalid,
  input  logic                          s_axi_wvalid,
  input  logic [31:0]                   s_axi_wdata,
  input  logic [3:0]                    s_axi_wstrb,
  input  logic                          s_axi_bready,
  input  logic [C_AXI_ADDR_WIDTH-1:0]   s_axi_araddr,
  input  logic [2:0]                    s_axi_arprot,
  input  logic                          s_axi_arvalid,
  input  logic                          s_axi_rready,

  output logic                          s_axi_awready,
  output logic                          s_axi_wready,
  output logic [1:0]                    s_axi_bresp,
  output logic                          s_axi_bvalid,
  output logic                          s_axi_arready,
  output logic [31:0]                   s_axi_rdata,
  output logic [1:0]                    s_axi_rresp,
  output logic                          s_axi_rvalid,

  // Master side
  output logic [C_AXI_ADDR_WIDTH-1:0]   m_axi_awaddr,
  output logic [2:0]                    m_axi_awprot,
  output logic                          m_axi_awvalid,
  output logic [63:0]                   m_axi_wdata,
  output logic [7:0]                    m_axi_wstrb,
  output logic                          m_axi_wvalid,
  output logic [C_AXI_ADDR_WIDTH-1:0]   m_axi_araddr,
  output logic [2:0]                    m_axi_arprot,
  output logic                          m_axi_arvalid,
  output logic                          m_axi_bready,
  output logic                          m_axi_rready,

  input  logic                          m_axi_awready,
  input  logic                          m_axi_wready,
  input  logic [1:0]                    m_axi_bresp,
  input  logic                          m_axi_bvalid,
  input  logic                          m_axi_arready,
  input  logic [63:0]                   m_axi_rdata,
  input  logic [1:0]                    m_axi_rresp,
  input  logic                          m_axi_rvalid,

  // Internal (bound hier refs)
  input  logic                          ar_done,
  input  logic                          aw_done,
  input  logic                          w_done,
  input  logic                          araddr2,
  input  logic                          s_axi_awready_i,
  input  logic                          s_axi_bvalid_i,
  input  logic                          s_axi_rvalid_i,
  input  logic                          m_axi_rready_i,
  input  logic                          m_axi_arvalid_i,
  input  logic                          m_axi_awvalid_i,
  input  logic                          m_axi_wvalid_i
);

  default clocking cb @(posedge aclk); endclocking
  default disable iff (!aresetn)

  // Environment assumptions: AXI-Lite stability while VALID && !READY (keeps assertions robust).
  // If you prefer pure checking, change 'assume' to 'assert'.
  assume property (C_AXI_SUPPORTS_READ  && (s_axi_arvalid && !s_axi_arready) |=> $stable(s_axi_araddr) && $stable(s_axi_arprot) && s_axi_arvalid);
  assume property (C_AXI_SUPPORTS_WRITE && (s_axi_awvalid && !s_axi_awready) |=> $stable(s_axi_awaddr) && $stable(s_axi_awprot) && s_axi_awvalid);
  assume property (C_AXI_SUPPORTS_WRITE && (s_axi_wvalid  && !s_axi_wready)  |=> $stable(s_axi_wdata) && $stable(s_axi_wstrb) && s_axi_wvalid);

  // Common passthrough checks
  assert property (C_AXI_SUPPORTS_READ  -> (m_axi_araddr == s_axi_araddr));
  assert property (C_AXI_SUPPORTS_READ  -> (m_axi_arprot == s_axi_arprot));
  assert property (C_AXI_SUPPORTS_WRITE -> (m_axi_awaddr == s_axi_awaddr));
  assert property (C_AXI_SUPPORTS_WRITE -> (m_axi_awprot == s_axi_awprot));

  // Read channel assertions
  if (C_AXI_SUPPORTS_READ) begin
    // Issue AR when requested and not busy
    assert property ((s_axi_arvalid && !ar_done) |=> m_axi_arvalid);

    // Only one outstanding read
    assert property (ar_done |-> !m_axi_arvalid);

    // s_axi_arready pulse corresponds to m-side AR handshake
    assert property ($rose(s_axi_arready) |-> $past(m_axi_arvalid && m_axi_arready));

    // araddr2 capture at m-side AR handshake
    assert property ((m_axi_arvalid && m_axi_arready) |=> araddr2 == $past(s_axi_araddr[2]));

    // RREADY only when s-side R handshake occurs
    assert property (m_axi_rready |-> (s_axi_rvalid && s_axi_rready));

    // Generate s_axi_rvalid when m-side RVALID and read outstanding
    assert property ((m_axi_rvalid && ar_done) |=> s_axi_rvalid);

    // s_axi_rvalid must hold until RREADY, then clear and clear ar_done, pulse m_axi_rready
    assert property ((s_axi_rvalid && !s_axi_rready) |=> s_axi_rvalid);
    assert property ((s_axi_rvalid && s_axi_rready) |=> (!s_axi_rvalid && !ar_done && m_axi_rready));

    // Data and resp mapping on R handshake
    assert property ((s_axi_rvalid && s_axi_rready) |-> s_axi_rresp == m_axi_rresp);
    assert property ((s_axi_rvalid && s_axi_rready) |-> s_axi_rdata == (araddr2 ? m_axi_rdata[63:32] : m_axi_rdata[31:0]));
  end else begin
    // No-read configuration outputs must be constant zero
    assert property (!m_axi_arvalid && !s_axi_arready && !s_axi_rvalid && !m_axi_rready &&
                     (s_axi_rresp == 2'b00) && (s_axi_rdata == 32'b0));
  end

  // Write channel assertions
  if (C_AXI_SUPPORTS_WRITE) begin
    // Issue AW when requested and not done
    assert property ((s_axi_awvalid && !aw_done) |=> m_axi_awvalid);
    // AW handshake sets aw_done and drops AWVALID
    assert property ((m_axi_awvalid && m_axi_awready) |=> (aw_done && !m_axi_awvalid));

    // Issue W when requested, AW is issued or done, and not done
    assert property ((s_axi_wvalid && (m_axi_awvalid || aw_done) && !w_done) |=> m_axi_wvalid);
    // W handshake sets w_done and drops WVALID
    assert property ((m_axi_wvalid && m_axi_wready) |=> (w_done && !m_axi_wvalid));

    // Once both AW and W are done, READY on S side only in response to BVALID
    assert property ((aw_done && w_done && m_axi_bvalid) |=> s_axi_awready);
    assert property ($rose(s_axi_awready) |-> $past(aw_done && w_done && m_axi_bvalid));

    // s_axi_bvalid generation and hold/clear
    assert property ($rose(s_axi_awready) |=> s_axi_bvalid);
    assert property ((s_axi_bvalid && !s_axi_bready) |=> s_axi_bvalid);
    assert property ((s_axi_bvalid && s_axi_bready) |=> !s_axi_bvalid);

    // m_axi_bready only when s-side B handshake
    assert property (m_axi_bready |-> (s_axi_bvalid && s_axi_bready));

    // BRESP passthrough at handshake
    assert property ((s_axi_bvalid && s_axi_bready) |-> (s_axi_bresp == m_axi_bresp));

    // WREADY equals AWREADY in this design
    assert property (s_axi_wready == s_axi_awready);

    // WDATA/WSTRB mapping
    assert property (m_axi_wvalid |-> (m_axi_wdata == {s_axi_wdata, s_axi_wdata}));
    assert property (m_axi_wvalid |-> (m_axi_wstrb == (s_axi_awaddr[2] ? {s_axi_wstrb, 4'b0000} : {4'b0000, s_axi_wstrb})));

    // While waiting for BRESP, no new AW/W issued
    assert property ((aw_done && w_done) |-> (!m_axi_awvalid && !m_axi_wvalid));
  end else begin
    // No-write configuration outputs must be constant zero
    assert property (!m_axi_awvalid && !s_axi_awready && !m_axi_wvalid && !s_axi_bvalid &&
                     !m_axi_bready && (m_axi_wdata == 64'b0) && (m_axi_wstrb == 8'b0) && (s_axi_bresp == 2'b00));
  end

  // Simple reset sanity (selective, concise)
  if (C_AXI_SUPPORTS_READ)  assert property (!$rose(aresetn) or m_axi_rready); // m_axi_rready comes up 1 after reset in RTL
  if (C_AXI_SUPPORTS_WRITE) assert property (!$rose(aresetn) or (!m_axi_awvalid && !m_axi_wvalid && !s_axi_bvalid));

  // Coverage
  if (C_AXI_SUPPORTS_READ) begin
    cover property (s_axi_arvalid && s_axi_arready ##[1:5] m_axi_rvalid ##1 s_axi_rvalid && s_axi_rready);
    cover property (s_axi_arvalid && s_axi_arready && (s_axi_araddr[2] == 1'b0));
    cover property (s_axi_arvalid && s_axi_arready && (s_axi_araddr[2] == 1'b1));
  end
  if (C_AXI_SUPPORTS_WRITE) begin
    cover property (s_axi_awvalid && s_axi_awready && s_axi_wvalid && s_axi_wready ##[1:5] s_axi_bvalid && s_axi_bready);
    cover property (s_axi_awvalid && s_axi_awready && (s_axi_awaddr[2] == 1'b0));
    cover property (s_axi_awvalid && s_axi_awready && (s_axi_awaddr[2] == 1'b1));
  end

endmodule

// Bind with hierarchical connections for internal regs
bind axi_dwidth_converter_v2_1_8_axi4lite_upsizer
  axi_dwidth_converter_v2_1_8_axi4lite_upsizer_sva #(
    .C_AXI_ADDR_WIDTH(C_AXI_ADDR_WIDTH),
    .C_AXI_SUPPORTS_WRITE(C_AXI_SUPPORTS_WRITE),
    .C_AXI_SUPPORTS_READ(C_AXI_SUPPORTS_READ)
  ) u_sva (
    .aclk(aclk),
    .aresetn(aresetn),

    .s_axi_awaddr(s_axi_awaddr),
    .s_axi_awprot(s_axi_awprot),
    .s_axi_awvalid(s_axi_awvalid),
    .s_axi_wvalid(s_axi_wvalid),
    .s_axi_wdata(s_axi_wdata),
    .s_axi_wstrb(s_axi_wstrb),
    .s_axi_bready(s_axi_bready),
    .s_axi_araddr(s_axi_araddr),
    .s_axi_arprot(s_axi_arprot),
    .s_axi_arvalid(s_axi_arvalid),
    .s_axi_rready(s_axi_rready),

    .s_axi_awready(s_axi_awready),
    .s_axi_wready(s_axi_wready),
    .s_axi_bresp(s_axi_bresp),
    .s_axi_bvalid(s_axi_bvalid),
    .s_axi_arready(s_axi_arready),
    .s_axi_rdata(s_axi_rdata),
    .s_axi_rresp(s_axi_rresp),
    .s_axi_rvalid(s_axi_rvalid),

    .m_axi_awaddr(m_axi_awaddr),
    .m_axi_awprot(m_axi_awprot),
    .m_axi_awvalid(m_axi_awvalid),
    .m_axi_wdata(m_axi_wdata),
    .m_axi_wstrb(m_axi_wstrb),
    .m_axi_wvalid(m_axi_wvalid),
    .m_axi_araddr(m_axi_araddr),
    .m_axi_arprot(m_axi_arprot),
    .m_axi_arvalid(m_axi_arvalid),
    .m_axi_bready(m_axi_bready),
    .m_axi_rready(m_axi_rready),

    .m_axi_awready(m_axi_awready),
    .m_axi_wready(m_axi_wready),
    .m_axi_bresp(m_axi_bresp),
    .m_axi_bvalid(m_axi_bvalid),
    .m_axi_arready(m_axi_arready),
    .m_axi_rdata(m_axi_rdata),
    .m_axi_rresp(m_axi_rresp),
    .m_axi_rvalid(m_axi_rvalid),

    // Internal hierarchy connections (names from DUT RTL)
    .ar_done(ar_done),
    .aw_done(aw_done),
    .w_done(w_done),
    .araddr2(araddr2),
    .s_axi_awready_i(s_axi_awready_i),
    .s_axi_bvalid_i(s_axi_bvalid_i),
    .s_axi_rvalid_i(s_axi_rvalid_i),
    .m_axi_rready_i(m_axi_rready_i),
    .m_axi_arvalid_i(m_axi_arvalid_i),
    .m_axi_awvalid_i(m_axi_awvalid_i),
    .m_axi_wvalid_i(m_axi_wvalid_i)
  );