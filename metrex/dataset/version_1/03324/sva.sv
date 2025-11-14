// SVA for AXI4LiteToRFBridgeVerilog
// Bindable, concise, protocol- and datapath-focused

module AXI4LiteToRFBridgeVerilog_sva #(
  parameter integer C_S_AXI_ADDR_WIDTH = 32,
  parameter integer C_S_AXI_DATA_WIDTH = 32
)(
  // treat all DUT ports as inputs for observation
  input  [C_S_AXI_ADDR_WIDTH-1:0] rf_raddr,
  input  [C_S_AXI_ADDR_WIDTH-1:0] rf_waddr,
  input                           rf_wen,
  input  [C_S_AXI_DATA_WIDTH-1:0] rf_wdata,
  input  [C_S_AXI_DATA_WIDTH-1:0] rf_rdata,

  input                           S_AXI_ACLK,
  input                           S_AXI_ARESETN,
  input  [C_S_AXI_ADDR_WIDTH-1:0] S_AXI_AWADDR,
  input  [2:0]                    S_AXI_AWPROT,
  input                           S_AXI_AWVALID,
  input                           S_AXI_AWREADY,
  input  [C_S_AXI_DATA_WIDTH-1:0] S_AXI_WDATA,
  input  [(C_S_AXI_DATA_WIDTH/8)-1:0] S_AXI_WSTRB,
  input                           S_AXI_WVALID,
  input                           S_AXI_WREADY,
  input  [1:0]                    S_AXI_BRESP,
  input                           S_AXI_BVALID,
  input                           S_AXI_BREADY,
  input  [C_S_AXI_ADDR_WIDTH-1:0] S_AXI_ARADDR,
  input  [2:0]                    S_AXI_ARPROT,
  input                           S_AXI_ARVALID,
  input                           S_AXI_ARREADY,
  input  [C_S_AXI_DATA_WIDTH-1:0] S_AXI_RDATA,
  input  [1:0]                    S_AXI_RRESP,
  input                           S_AXI_RVALID,
  input                           S_AXI_RREADY
);

  // mirror DUT constants
  localparam int ADDR_LSB = (C_S_AXI_DATA_WIDTH/32) + 1;
  localparam int OPT_MEM_ADDR_BITS = 16;
  localparam int LO = ADDR_LSB;
  localparam int HI = ADDR_LSB + OPT_MEM_ADDR_BITS;

  default clocking cb @(posedge S_AXI_ACLK); endclocking
  default disable iff (!S_AXI_ARESETN);

  // Optional: constrain master (uncomment for formal/sim environments)
  // assume property (S_AXI_AWVALID && !S_AXI_AWREADY |=> S_AXI_AWVALID);
  // assume property (S_AXI_WVALID  && !S_AXI_WREADY  |=> S_AXI_WVALID);
  // assume property (S_AXI_ARVALID && !S_AXI_ARREADY |=> S_AXI_ARVALID);

  // Ready implies valid
  assert property (S_AXI_AWREADY |-> (S_AXI_AWVALID && S_AXI_WVALID));
  assert property (S_AXI_WREADY  |-> (S_AXI_AWVALID && S_AXI_WVALID));
  assert property (S_AXI_ARREADY |->  S_AXI_ARVALID);

  // Single-cycle ready pulses
  assert property (S_AXI_AWREADY |=> !S_AXI_AWREADY);
  assert property (S_AXI_WREADY  |=> !S_AXI_WREADY);
  assert property (S_AXI_ARREADY |=> !S_AXI_ARREADY);

  // Write accept event
  sequence wr_acc; S_AXI_AWVALID && S_AXI_AWREADY && S_AXI_WVALID && S_AXI_WREADY; endsequence
  // Read accept event
  sequence rd_acc; S_AXI_ARVALID && S_AXI_ARREADY; endsequence

  // No multiple outstanding (AXI4-Lite)
  assert property (wr_acc |-> (!wr_acc) until_with (S_AXI_BVALID && S_AXI_BREADY));
  assert property (rd_acc |-> (!rd_acc) until_with (S_AXI_RVALID && S_AXI_RREADY));

  // Do not accept AR while read data outstanding
  assert property (S_AXI_RVALID |-> !S_AXI_ARREADY);

  // Responses generated promptly and OKAY
  assert property (wr_acc |=> (S_AXI_BVALID && S_AXI_BRESP == 2'b00));
  assert property (S_AXI_BVALID && !S_AXI_BREADY |=> S_AXI_BVALID);
  assert property (S_AXI_BVALID |-> S_AXI_BRESP == 2'b00);

  assert property (rd_acc && !S_AXI_RVALID |=> (S_AXI_RVALID && S_AXI_RRESP == 2'b00));
  assert property (S_AXI_RVALID && !S_AXI_RREADY |=> S_AXI_RVALID);
  assert property (S_AXI_RVALID |-> S_AXI_RRESP == 2'b00);

  // Register file write side mapping
  assert property (wr_acc |-> rf_wen);
  assert property (rf_wen |-> (rf_wdata == S_AXI_WDATA));
  // Address arrives to RF one cycle after acceptance (DUT latches address)
  assert property (wr_acc |=> rf_waddr == $past(S_AXI_AWADDR)[HI:LO]);

  // Register file read side mapping and data return
  // Address presented to RF one cycle after AR accept
  assert property (rd_acc |=> rf_raddr == $past(S_AXI_ARADDR)[HI:LO]);
  // Data captured into RDATA one cycle after slv_reg_rden (i.e., AR accept when !RVALID)
  assert property ((S_AXI_ARREADY && S_AXI_ARVALID && !S_AXI_RVALID) |=> (S_AXI_RVALID && S_AXI_RDATA == $past(rf_rdata)));

  // Basic X checks on critical outputs
  assert property (!$isunknown({S_AXI_AWREADY,S_AXI_WREADY,S_AXI_ARREADY,S_AXI_BVALID,S_AXI_RVALID,S_AXI_BRESP,S_AXI_RRESP,rf_wen})));

  // Coverage
  cover property (wr_acc ##1 S_AXI_BVALID ##[1:10] S_AXI_BREADY);
  cover property (rd_acc ##1 S_AXI_RVALID ##[1:10] S_AXI_RREADY);
  cover property (wr_acc ##1 rd_acc);
  cover property (rd_acc ##1 wr_acc);
  cover property (S_AXI_BVALID && !S_AXI_BREADY [*3] ##1 S_AXI_BREADY);
  cover property (S_AXI_RVALID && !S_AXI_RREADY [*3] ##1 S_AXI_RREADY);

  // Optional: cover potential protocol weakness (multiple accepts before response)
  cover property (wr_acc ##1 (!S_AXI_BVALID)[*1:5] ##1 wr_acc);

endmodule

// Bind into DUT
bind AXI4LiteToRFBridgeVerilog
  AXI4LiteToRFBridgeVerilog_sva #(
    .C_S_AXI_ADDR_WIDTH(C_S_AXI_ADDR_WIDTH),
    .C_S_AXI_DATA_WIDTH(C_S_AXI_DATA_WIDTH)
  ) i_AXIL2RF_SVA (.*);