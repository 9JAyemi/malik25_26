// SVA checker for axi_bram_reader
// Concise, high-signal-coverage assertions and key covers.
// Bind into your DUT with:  bind axi_bram_reader axi_bram_reader_sva #(.AXI_DATA_WIDTH(AXI_DATA_WIDTH), .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH), .BRAM_DATA_WIDTH(BRAM_DATA_WIDTH), .BRAM_ADDR_WIDTH(BRAM_ADDR_WIDTH)) axi_bram_reader_sva_i (.*);

module axi_bram_reader_sva #
(
  parameter int AXI_DATA_WIDTH = 32,
  parameter int AXI_ADDR_WIDTH = 16,
  parameter int BRAM_DATA_WIDTH = 32,
  parameter int BRAM_ADDR_WIDTH = 10
)
(
  input  logic                       aclk,
  input  logic                       aresetn,

  input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_awaddr,
  input  logic                       s_axi_awvalid,
  output logic                       s_axi_awready,
  input  logic [AXI_DATA_WIDTH-1:0]  s_axi_wdata,
  input  logic                       s_axi_wvalid,
  output logic                       s_axi_wready,
  output logic [1:0]                 s_axi_bresp,
  output logic                       s_axi_bvalid,
  input  logic                       s_axi_bready,
  input  logic [AXI_ADDR_WIDTH-1:0]  s_axi_araddr,
  input  logic                       s_axi_arvalid,
  output logic                       s_axi_arready,
  output logic [AXI_DATA_WIDTH-1:0]  s_axi_rdata,
  output logic [1:0]                 s_axi_rresp,
  output logic                       s_axi_rvalid,
  input  logic                       s_axi_rready,

  output logic                       bram_porta_clk,
  output logic                       bram_porta_rst,
  output logic [BRAM_ADDR_WIDTH-1:0] bram_porta_addr,
  input  logic [BRAM_DATA_WIDTH-1:0] bram_porta_rddata
);

  localparam int ADDR_LSB = $clog2(AXI_DATA_WIDTH/8);

  default clocking cb @(posedge aclk); endclocking

  // Track a single queued AR address accepted while R is stalled
  logic                        queued_pending;
  logic [AXI_ADDR_WIDTH-1:0]   queued_addr;

  always_ff @(posedge aclk or negedge aresetn) begin
    if (!aresetn) begin
      queued_pending <= 1'b0;
      queued_addr    <= '0;
    end else begin
      // Capture AR when R is stalled
      if (s_axi_rvalid && !s_axi_rready && s_axi_arvalid && s_axi_arready) begin
        queued_pending <= 1'b1;
        queued_addr    <= s_axi_araddr;
      end
      // Clear when read completes
      if (s_axi_rvalid && s_axi_rready) begin
        queued_pending <= 1'b0;
      end
    end
  end

  // Reset behavior
  assert property (@(posedge aclk) !aresetn |-> (s_axi_arready && !s_axi_rvalid && s_axi_rresp==2'd0 &&
                                                 s_axi_awready==1'b0 && s_axi_wready==1'b0 &&
                                                 s_axi_bvalid==1'b0 && s_axi_bresp==2'd0));

  // Constant/structural ties
  assert property (s_axi_awready==1'b0);
  assert property (s_axi_wready==1'b0);
  assert property (s_axi_bvalid==1'b0);
  assert property (s_axi_bresp==2'd0);
  assert property (s_axi_rresp==2'd0);
  assert property (s_axi_rdata == bram_porta_rddata);
  assert property (@(posedge aclk) bram_porta_rst == ~aresetn);
  // bram clock follows aclk on both edges
  assert property (@(posedge aclk)  bram_porta_clk);
  assert property (@(negedge aclk) !bram_porta_clk);

  // No write-channel handshakes can ever occur
  assert property (@(posedge aclk) !(s_axi_awvalid && s_axi_awready));
  assert property (@(posedge aclk) !(s_axi_wvalid  && s_axi_wready));
  assert property (@(posedge aclk) !(s_axi_bvalid  && s_axi_bready));

  // Outputs are never X/Z after reset deasserts
  assert property (@(posedge aclk) disable iff (!aresetn)
                   !$isunknown({s_axi_arready, s_axi_rvalid, s_axi_rresp,
                                s_axi_awready, s_axi_wready, s_axi_bvalid,
                                bram_porta_rst, bram_porta_addr}));

  // ARREADY is high whenever there is no outstanding RVALID
  assert property (@(posedge aclk) disable iff (!aresetn)
                   (!s_axi_rvalid) |-> s_axi_arready);

  // Read-channel handshake behavior
  // 1) If AR handshakes when no RVALID pending, RVALID asserts next cycle
  assert property (@(posedge aclk) disable iff (!aresetn)
                   (s_axi_arvalid && s_axi_arready && !s_axi_rvalid) |=> s_axi_rvalid);

  // 2) RVALID holds until RREADY
  assert property (@(posedge aclk) disable iff (!aresetn)
                   (s_axi_rvalid && !s_axi_rready) |=> s_axi_rvalid);

  // 3) A rising RVALID must be caused by either an AR handshake in prev cycle or an earlier queued AR
  assert property (@(posedge aclk) disable iff (!aresetn)
                   $rose(s_axi_rvalid) |-> ($past(s_axi_arvalid && s_axi_arready) || $past(queued_pending)));

  // Backpressure and queueing rules
  // When R is stalled and ARVALID is asserted, ARREADY must drop next cycle (to cap queue depth)
  assert property (@(posedge aclk) disable iff (!aresetn)
                   (s_axi_rvalid && !s_axi_rready && s_axi_arvalid) |=> !s_axi_arready);

  // Once an AR is queued during a stall, no further AR handshakes until the read completes
  assert property (@(posedge aclk) disable iff (!aresetn)
                   queued_pending |-> !(s_axi_arvalid && s_axi_arready));

  // BRAM address behavior
  // 1) When R is stalled, BRAM address must hold stable
  assert property (@(posedge aclk) disable iff (!aresetn)
                   (s_axi_rvalid && !s_axi_rready) |=> $stable(bram_porta_addr));

  // 2) If AR handshakes with no pending RVALID, BRAM addr reflects ARADDR (word-aligned) in the same cycle
  assert property (@(posedge aclk) disable iff (!aresetn)
                   (s_axi_arvalid && s_axi_arready && !s_axi_rvalid)
                   |-> (bram_porta_addr == s_axi_araddr[ADDR_LSB+BRAM_ADDR_WIDTH-1:ADDR_LSB]));

  // 3) If an AR was queued during a stall, on the cycle the stalled R completes, BRAM addr updates to queued addr
  assert property (@(posedge aclk) disable iff (!aresetn)
                   (s_axi_rvalid && s_axi_rready && queued_pending)
                   |-> (bram_porta_addr == queued_addr[ADDR_LSB+BRAM_ADDR_WIDTH-1:ADDR_LSB]));

  // Coverage
  // Basic read transaction
  cover property (@(posedge aclk) disable iff (!aresetn)
                  s_axi_arvalid && s_axi_arready ##1 s_axi_rvalid ##1 s_axi_rvalid && s_axi_rready);

  // Back-to-back reads without backpressure
  cover property (@(posedge aclk) disable iff (!aresetn)
                  (s_axi_arvalid && s_axi_arready && !s_axi_rvalid)
                  ##1 (s_axi_rvalid && s_axi_rready)
                  ##1 (s_axi_arvalid && s_axi_arready)
                  ##1 (s_axi_rvalid && s_axi_rready));

  // Queue during stall, then complete
  cover property (@(posedge aclk) disable iff (!aresetn)
                  (s_axi_arvalid && s_axi_arready) ##1
                  (s_axi_rvalid && !s_axi_rready) [*2:$] ##1
                  (s_axi_arvalid && s_axi_arready) ##1
                  (s_axi_rvalid && s_axi_rready));

endmodule