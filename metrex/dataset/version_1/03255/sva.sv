// SVA checker for tb_axil_slave_model
module tb_axil_slave_model_sva (
  input            ARESETN,
  input            ACLK,

  input  [31:0]    M_AXI_AWADDR,
  input  [3:0]     M_AXI_AWCACHE,
  input  [2:0]     M_AXI_AWPROT,
  input            M_AXI_AWVALID,
  input            M_AXI_AWREADY,

  input  [31:0]    M_AXI_WDATA,
  input  [3:0]     M_AXI_WSTRB,
  input            M_AXI_WVALID,
  input            M_AXI_WREADY,

  input  [1:0]     M_AXI_BRESP,
  input            M_AXI_BVALID,
  input            M_AXI_BREADY,

  input  [31:0]    M_AXI_ARADDR,
  input  [3:0]     M_AXI_ARCACHE,
  input  [2:0]     M_AXI_ARPROT,
  input            M_AXI_ARVALID,
  input            M_AXI_ARREADY,

  input  [31:0]    M_AXI_RDATA,
  input  [1:0]     M_AXI_RRESP,
  input            M_AXI_RVALID,
  input            M_AXI_RREADY
);

  default clocking cb @(posedge ACLK); endclocking
  default disable iff (!ARESETN)

  // Simple scoreboard for pending transactions
  logic wpend, rpend;
  logic [31:0] araddr_req;

  always @(posedge ACLK or negedge ARESETN) begin
    if (!ARESETN) begin
      wpend      <= 1'b0;
      rpend      <= 1'b0;
      araddr_req <= '0;
    end else begin
      if (M_AXI_WVALID && M_AXI_WREADY) wpend <= 1'b1;
      if (M_AXI_BVALID && M_AXI_BREADY) wpend <= 1'b0;

      if (M_AXI_ARVALID && M_AXI_ARREADY) begin
        rpend      <= 1'b1;
        araddr_req <= M_AXI_ARADDR;
      end
      if (M_AXI_RVALID && M_AXI_RREADY) rpend <= 1'b0;
    end
  end

  // Basic sanity/X checks
  assert property (!$isunknown({M_AXI_AWREADY,M_AXI_WREADY,M_AXI_ARREADY,
                                M_AXI_BVALID,M_AXI_RVALID,M_AXI_BRESP,M_AXI_RRESP,M_AXI_RDATA})));

  // Static, always-ready outputs for this model
  assert property (M_AXI_AWREADY && M_AXI_WREADY && M_AXI_ARREADY);
  assert property ($stable({M_AXI_AWREADY,M_AXI_WREADY,M_AXI_ARREADY}));

  // Fixed OKAY responses
  assert property (M_AXI_BRESP == 2'b00);
  assert property (M_AXI_RRESP == 2'b00);

  // Write response channel behavior
  // BVALID mirrors pending write and holds until BREADY
  assert property (M_AXI_BVALID == wpend);
  assert property ((M_AXI_WVALID && M_AXI_WREADY) |=> M_AXI_BVALID);
  assert property ((M_AXI_BVALID && !M_AXI_BREADY) |=> M_AXI_BVALID);
  assert property ((M_AXI_BVALID && M_AXI_BREADY) |=> !M_AXI_BVALID);
  // No new write data handshakes while response pending (model cannot queue)
  assert property (wpend |-> !(M_AXI_WVALID && M_AXI_WREADY));

  // Read response channel behavior
  // RVALID only when RREADY and a read is pending
  assert property (M_AXI_RVALID == (rpend && M_AXI_RREADY));
  assert property (M_AXI_RVALID |-> M_AXI_RREADY);
  assert property ((M_AXI_RVALID && M_AXI_RREADY) |=> !M_AXI_RVALID);
  // No new AR handshakes while a read is pending (model cannot queue)
  assert property (rpend |-> !(M_AXI_ARVALID && M_AXI_ARREADY));
  // Keep ARADDR stable while read pending so echo RDATA is consistent
  assert property (rpend |-> $stable(M_AXI_ARADDR));
  // Return data must match captured ARADDR at the read handshake
  assert property ((M_AXI_RVALID && M_AXI_RREADY) |-> (M_AXI_RDATA == araddr_req));

  // Minimal protocol covers
  cover property (M_AXI_AWVALID && M_AXI_AWREADY);
  cover property ((M_AXI_WVALID && M_AXI_WREADY) ##[1:5] (M_AXI_BVALID && M_AXI_BREADY));
  cover property ((M_AXI_ARVALID && M_AXI_ARREADY) ##[1:5] (M_AXI_RREADY && M_AXI_RVALID));
  // Read with backpressure before response
  cover property ((M_AXI_ARVALID && M_AXI_ARREADY) ##1 (!M_AXI_RREADY)[*2:10] ##1 (M_AXI_RREADY && M_AXI_RVALID));

endmodule

// Bind into DUT
bind tb_axil_slave_model tb_axil_slave_model_sva sva_i (
  .ARESETN(ARESETN),
  .ACLK(ACLK),
  .M_AXI_AWADDR(M_AXI_AWADDR),
  .M_AXI_AWCACHE(M_AXI_AWCACHE),
  .M_AXI_AWPROT(M_AXI_AWPROT),
  .M_AXI_AWVALID(M_AXI_AWVALID),
  .M_AXI_AWREADY(M_AXI_AWREADY),
  .M_AXI_WDATA(M_AXI_WDATA),
  .M_AXI_WSTRB(M_AXI_WSTRB),
  .M_AXI_WVALID(M_AXI_WVALID),
  .M_AXI_WREADY(M_AXI_WREADY),
  .M_AXI_BRESP(M_AXI_BRESP),
  .M_AXI_BVALID(M_AXI_BVALID),
  .M_AXI_BREADY(M_AXI_BREADY),
  .M_AXI_ARADDR(M_AXI_ARADDR),
  .M_AXI_ARCACHE(M_AXI_ARCACHE),
  .M_AXI_ARPROT(M_AXI_ARPROT),
  .M_AXI_ARVALID(M_AXI_ARVALID),
  .M_AXI_ARREADY(M_AXI_ARREADY),
  .M_AXI_RDATA(M_AXI_RDATA),
  .M_AXI_RRESP(M_AXI_RRESP),
  .M_AXI_RVALID(M_AXI_RVALID),
  .M_AXI_RREADY(M_AXI_RREADY)
);