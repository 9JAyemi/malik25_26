// SVA for axi_protocol_converter_v2_1_7_decerr_slave
// Concise, protocol- and implementation-aware checks with basic coverage.

module axi_protocol_converter_v2_1_7_decerr_slave_sva #(
  parameter integer C_AXI_ID_WIDTH    = 1,
  parameter integer C_AXI_DATA_WIDTH  = 32,
  parameter integer C_AXI_BUSER_WIDTH = 1,
  parameter integer C_AXI_RUSER_WIDTH = 1,
  parameter integer C_AXI_PROTOCOL    = 0,
  parameter [1:0]   C_RESP            = 2'b11,
  parameter integer C_IGNORE_ID       = 0
)(
  input  wire                              ACLK,
  input  wire                              ARESETN,
  input  wire [C_AXI_ID_WIDTH-1:0]         S_AXI_AWID,
  input  wire                              S_AXI_AWVALID,
  input  wire                              S_AXI_WLAST,
  input  wire                              S_AXI_WVALID,
  input  wire                              S_AXI_BREADY,
  input  wire [C_AXI_ID_WIDTH-1:0]         S_AXI_ARID,
  input  wire [((C_AXI_PROTOCOL == 1) ? 4 : 8)-1:0] S_AXI_ARLEN,
  input  wire                              S_AXI_ARVALID,
  input  wire                              S_AXI_RREADY,
  output wire                              S_AXI_AWREADY,
  output wire                              S_AXI_WREADY,
  output wire [C_AXI_ID_WIDTH-1:0]         S_AXI_BID,
  output wire [1:0]                        S_AXI_BRESP,
  output wire [C_AXI_BUSER_WIDTH-1:0]      S_AXI_BUSER,
  output wire                              S_AXI_BVALID,
  output wire                              S_AXI_ARREADY,
  output wire [C_AXI_ID_WIDTH-1:0]         S_AXI_RID,
  output wire [C_AXI_DATA_WIDTH-1:0]       S_AXI_RDATA,
  output wire [1:0]                        S_AXI_RRESP,
  output wire [C_AXI_RUSER_WIDTH-1:0]      S_AXI_RUSER,
  output wire                              S_AXI_RLAST,
  output wire                              S_AXI_RVALID
);
  localparam integer P_AXI4    = 0;
  localparam integer P_AXI3    = 1;
  localparam integer P_AXILITE = 2;

  default clocking cb @(posedge ACLK); endclocking
  default disable iff (!ARESETN)

  // Constant response/data/user on valid
  assert property (S_AXI_BVALID |-> (S_AXI_BRESP == C_RESP && S_AXI_BUSER == {C_AXI_BUSER_WIDTH{1'b0}}));
  assert property (S_AXI_RVALID |-> (S_AXI_RRESP == C_RESP && S_AXI_RUSER == {C_AXI_RUSER_WIDTH{1'b0}} && S_AXI_RDATA == {C_AXI_DATA_WIDTH{1'b0}}));

  // VALID must hold until handshake; payload stable while waiting
  assert property (S_AXI_BVALID |-> S_AXI_BVALID until_with S_AXI_BREADY);
  assert property (S_AXI_RVALID |-> S_AXI_RVALID until_with S_AXI_RREADY);
  assert property (S_AXI_BVALID && !S_AXI_BREADY |-> $stable({S_AXI_BVALID,S_AXI_BRESP,S_AXI_BID,S_AXI_BUSER})));
  assert property (S_AXI_RVALID && !S_AXI_RREADY |-> $stable({S_AXI_RVALID,S_AXI_RRESP,S_AXI_RID,S_AXI_RUSER,S_AXI_RLAST,S_AXI_RDATA})));

  // RLAST only when RVALID
  assert property (S_AXI_RLAST |-> S_AXI_RVALID);

  // Ready gating (no new addr while data/resp active)
  assert property (S_AXI_AWREADY |-> (!S_AXI_WREADY && !S_AXI_BVALID));
  assert property (S_AXI_ARREADY |-> (!S_AXI_RVALID));

  // ID behavior
  generate
    if (C_IGNORE_ID == 0) begin
      // Single outstanding ensures “last handshake” mapping works
      assert property (S_AXI_BVALID |-> S_AXI_BID == $past(S_AXI_AWID, 1, S_AXI_AWVALID && S_AXI_AWREADY));
      assert property (S_AXI_RVALID |-> S_AXI_RID == $past(S_AXI_ARID, 1, S_AXI_ARVALID && S_AXI_ARREADY));
    end else begin
      assert property (S_AXI_BVALID |-> S_AXI_BID == '0);
      assert property (S_AXI_RVALID |-> S_AXI_RID == '0);
    end
  endgenerate

  // Channel causality
  if (C_AXI_PROTOCOL == P_AXILITE) begin
    assert property ($rose(S_AXI_BVALID) |-> $past(S_AXI_WVALID && S_AXI_WREADY, 1));
    assert property ($rose(S_AXI_RVALID) |-> $past(S_AXI_ARVALID && S_AXI_ARREADY, 1));
    assert property (S_AXI_RVALID |-> S_AXI_RLAST); // AXI-Lite: single-beat reads
  end else begin
    assert property ($rose(S_AXI_BVALID) |-> $past(S_AXI_WVALID && S_AXI_WREADY && S_AXI_WLAST, 1));
    assert property ($rose(S_AXI_RVALID) |-> $past(S_AXI_ARVALID && S_AXI_ARREADY, 1));

    // First R beat RLAST depends on ARLEN==0
    assert property ($rose(S_AXI_RVALID) |-> S_AXI_RLAST == $past(S_AXI_ARLEN == '0, 1));

    // During a burst, eventually one last beat occurs before deasserting RVALID
    assert property ($rose(S_AXI_RVALID) |-> (S_AXI_RVALID && !S_AXI_RLAST)[*0:$] ##1 (S_AXI_RVALID && S_AXI_RLAST));
  end

  // Basic functional coverage
  // Write transaction completes
  cover property (S_AXI_AWVALID && S_AXI_AWREADY
                  ##[1:10] S_AXI_WVALID && S_AXI_WREADY && (C_AXI_PROTOCOL==P_AXILITE ? 1'b1 : S_AXI_WLAST)
                  ##[1:10] S_AXI_BVALID && S_AXI_BREADY);

  // Read single-beat (len==0) completes
  cover property (S_AXI_ARVALID && S_AXI_ARREADY && (S_AXI_ARLEN=='0)
                  ##[1:5] S_AXI_RVALID && S_AXI_RLAST
                  ##[0:5] S_AXI_RREADY);

  // Read multi-beat (len>0) completes with RLAST on last
  cover property (S_AXI_ARVALID && S_AXI_ARREADY && (S_AXI_ARLEN!='0)
                  ##[1:5] $rose(S_AXI_RVALID)
                  ##[1:32] (S_AXI_RVALID && S_AXI_RLAST) ##1 !S_AXI_RVALID);

endmodule

bind axi_protocol_converter_v2_1_7_decerr_slave
  axi_protocol_converter_v2_1_7_decerr_slave_sva #(
    .C_AXI_ID_WIDTH(C_AXI_ID_WIDTH),
    .C_AXI_DATA_WIDTH(C_AXI_DATA_WIDTH),
    .C_AXI_BUSER_WIDTH(C_AXI_BUSER_WIDTH),
    .C_AXI_RUSER_WIDTH(C_AXI_RUSER_WIDTH),
    .C_AXI_PROTOCOL(C_AXI_PROTOCOL),
    .C_RESP(C_RESP),
    .C_IGNORE_ID(C_IGNORE_ID)
  ) u_axi_protocol_converter_v2_1_7_decerr_slave_sva (.*);