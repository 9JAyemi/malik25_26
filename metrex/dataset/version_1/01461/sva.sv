// SVA for fmrv32im_axim
// Bind this module to the DUT:
// bind fmrv32im_axim fmrv32im_axim_sva sva (.*);

module fmrv32im_axim_sva
(
  input         RST_N,
  input         CLK,

  input  [0:0]  M_AXI_AWID,
  input  [31:0] M_AXI_AWADDR,
  input  [7:0]  M_AXI_AWLEN,
  input  [2:0]  M_AXI_AWSIZE,
  input  [1:0]  M_AXI_AWBURST,
  input         M_AXI_AWLOCK,
  input  [3:0]  M_AXI_AWCACHE,
  input  [2:0]  M_AXI_AWPROT,
  input  [3:0]  M_AXI_AWQOS,
  input  [0:0]  M_AXI_AWUSER,
  input         M_AXI_AWVALID,
  input         M_AXI_AWREADY,

  input  [31:0] M_AXI_WDATA,
  input  [3:0]  M_AXI_WSTRB,
  input         M_AXI_WLAST,
  input  [0:0]  M_AXI_WUSER,
  input         M_AXI_WVALID,
  input         M_AXI_WREADY,

  input  [0:0]  M_AXI_BID,
  input  [1:0]  M_AXI_BRESP,
  input  [0:0]  M_AXI_BUSER,
  input         M_AXI_BVALID,
  input         M_AXI_BREADY,

  input  [0:0]  M_AXI_ARID,
  input  [31:0] M_AXI_ARADDR,
  input  [7:0]  M_AXI_ARLEN,
  input  [2:0]  M_AXI_ARSIZE,
  input  [1:0]  M_AXI_ARBURST,
  input  [1:0]  M_AXI_ARLOCK,
  input  [3:0]  M_AXI_ARCACHE,
  input  [2:0]  M_AXI_ARPROT,
  input  [3:0]  M_AXI_ARQOS,
  input  [0:0]  M_AXI_ARUSER,
  input         M_AXI_ARVALID,
  input         M_AXI_ARREADY,

  input  [0:0]  M_AXI_RID,
  input  [31:0] M_AXI_RDATA,
  input  [1:0]  M_AXI_RRESP,
  input         M_AXI_RLAST,
  input  [0:0]  M_AXI_RUSER,
  input         M_AXI_RVALID,
  input         M_AXI_RREADY,

  input         WR_REQ_START,
  input [31:0]  WR_REQ_ADDR,
  input [15:0]  WR_REQ_LEN,
  input         WR_REQ_READY,
  input [9:0]   WR_REQ_MEM_ADDR,
  input [31:0]  WR_REQ_MEM_WDATA,

  input         RD_REQ_START,
  input [31:0]  RD_REQ_ADDR,
  input [15:0]  RD_REQ_LEN,
  input         RD_REQ_READY,
  input         RD_REQ_MEM_WE,
  input [9:0]   RD_REQ_MEM_ADDR,
  input [31:0]  RD_REQ_MEM_RDATA
);

  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RST_N)

  wire aw_fire = M_AXI_AWVALID && M_AXI_AWREADY;
  wire w_fire  = M_AXI_WVALID  && M_AXI_WREADY;
  wire ar_fire = M_AXI_ARVALID && M_AXI_ARREADY;
  wire r_fire  = M_AXI_RVALID  && M_AXI_RREADY;

  // AXI channel stability while waiting
  assert property (M_AXI_AWVALID && !M_AXI_AWREADY |-> $stable({M_AXI_AWADDR,M_AXI_AWLEN,M_AXI_AWSIZE,M_AXI_AWBURST,M_AXI_AWLOCK,M_AXI_AWCACHE,M_AXI_AWPROT,M_AXI_AWQOS,M_AXI_AWUSER,M_AXI_AWID})));
  assert property (M_AXI_WVALID  && !M_AXI_WREADY  |-> $stable({M_AXI_WDATA,M_AXI_WSTRB,M_AXI_WLAST,M_AXI_WUSER})));
  assert property (M_AXI_ARVALID && !M_AXI_ARREADY |-> $stable({M_AXI_ARADDR,M_AXI_ARLEN,M_AXI_ARSIZE,M_AXI_ARBURST,M_AXI_ARLOCK,M_AXI_ARCACHE,M_AXI_ARPROT,M_AXI_ARQOS,M_AXI_ARUSER,M_AXI_ARID})));

  // Constant fields and alignment when valid
  assert property (M_AXI_AWVALID |-> (M_AXI_AWSIZE==3'b010 && M_AXI_AWBURST==2'b01 && M_AXI_AWLOCK==1'b0 && M_AXI_AWCACHE==4'b0011 && M_AXI_AWPROT==3'b000 && M_AXI_AWQOS==4'b0000 && M_AXI_AWUSER==1'b1 && M_AXI_AWID==1'b0 && M_AXI_AWADDR[1:0]==2'b00));
  assert property (M_AXI_WVALID  |-> (M_AXI_WSTRB==4'hF));
  assert property (M_AXI_ARVALID |-> (M_AXI_ARSIZE==3'b010 && M_AXI_ARBURST==2'b01 && M_AXI_ARLOCK==2'b00 && M_AXI_ARCACHE==4'b0011 && M_AXI_ARPROT==3'b000 && M_AXI_ARQOS==4'b0000 && M_AXI_ARUSER==1'b1 && M_AXI_ARID==1'b0 && M_AXI_ARADDR[1:0]==2'b00));

  // RREADY is constant 1
  assert property (M_AXI_RREADY);

  // Protocol linking
  assert property (aw_fire |=> M_AXI_WVALID);                       // WVALID starts after AW handshake
  assert property (M_AXI_WLAST |-> M_AXI_WVALID);                   // WLAST only with WVALID
  assert property (M_AXI_BVALID |-> M_AXI_BREADY);                  // Always ready to accept response when it arrives
  assert property (WR_REQ_START && WR_REQ_READY |=> M_AXI_AWVALID); // Write request triggers AW
  assert property (RD_REQ_START && RD_REQ_READY |=> M_AXI_ARVALID); // Read request triggers AR
  assert property (RD_REQ_MEM_WE == M_AXI_RVALID);                  // Memory WE follows RVALID

  // No write data before address accepted
  logic aw_seen;
  always_ff @(posedge CLK or negedge RST_N) begin
    if (!RST_N) aw_seen <= 1'b0;
    else if (aw_fire) aw_seen <= 1'b1;
    else if (M_AXI_BVALID && M_AXI_BREADY) aw_seen <= 1'b0;
  end
  assert property (!aw_seen |-> !M_AXI_WVALID); // No WVALID until some AW has been accepted

  // Write burst beat counting: beats = AWLEN+1, WLAST on final beat
  logic        w_active;
  int unsigned w_expected;
  int unsigned w_count;
  always_ff @(posedge CLK or negedge RST_N) begin
    if (!RST_N) begin
      w_active   <= 1'b0;
      w_expected <= '0;
      w_count    <= '0;
    end else begin
      if (aw_fire) begin
        assert (!w_active) else $error("AW while previous write burst active");
        w_active   <= 1'b1;
        w_expected <= M_AXI_AWLEN + 1;
        w_count    <= 0;
      end
      if (w_active && w_fire) begin
        w_count <= w_count + 1;
        if (M_AXI_WLAST) begin
          assert (w_count + 1 == w_expected) else $error("WLAST not on expected final write beat");
          w_active <= 1'b0;
        end else begin
          assert (w_count + 1 < w_expected) else $error("Too many write beats without WLAST");
        end
      end
      if (M_AXI_BVALID && M_AXI_BREADY) begin
        // ensure write channel not active after response
        assert (!w_active) else $error("Write active when B channel responded");
      end
    end
  end

  // Read burst beat counting: beats = ARLEN+1, RLAST on final beat
  logic        r_active;
  int unsigned r_expected;
  int unsigned r_count;
  always_ff @(posedge CLK or negedge RST_N) begin
    if (!RST_N) begin
      r_active   <= 1'b0;
      r_expected <= '0;
      r_count    <= '0;
    end else begin
      if (ar_fire) begin
        assert (!r_active) else $error("AR while previous read burst active");
        r_active   <= 1'b1;
        r_expected <= M_AXI_ARLEN + 1;
        r_count    <= 0;
      end
      if (r_active && r_fire) begin
        r_count <= r_count + 1;
        if (M_AXI_RLAST) begin
          assert (r_count == r_expected) else $error("RLAST not on expected final read beat");
          r_active <= 1'b0;
        end else begin
          assert (r_count < r_expected) else $error("Too many read beats without RLAST");
        end
      end
    end
  end

  // Coverage: single-beat and max bursts, multi-burst sequences, address stride continuation
  cover property (aw_fire && (M_AXI_AWLEN==8'd0));
  cover property (aw_fire && (M_AXI_AWLEN==8'hFF));
  cover property (aw_fire ##[1:$] (M_AXI_BVALID && M_AXI_BREADY) ##1 aw_fire); // back-to-back write bursts
  cover property (ar_fire && (M_AXI_ARLEN==8'd0));
  cover property (ar_fire && (M_AXI_ARLEN==8'hFF));
  cover property (ar_fire ##[1:$] ar_fire); // back-to-back read bursts

  // Coverage: write continuation with +1024 stride (if slave accepts)
  cover property (aw_fire ##[1:$] (M_AXI_BVALID && M_AXI_BREADY) ##1 aw_fire && (M_AXI_AWADDR == $past(M_AXI_AWADDR,1) + 32'd1024));

  // Coverage: read continuation with +1024 stride
  cover property (ar_fire ##[1:$] (M_AXI_RVALID && M_AXI_RLAST && M_AXI_RREADY) ##1 ar_fire && (M_AXI_ARADDR == $past(M_AXI_ARADDR,1) + 32'd1024));

endmodule