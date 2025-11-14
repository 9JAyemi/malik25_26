// SVA for zbroji_HLS_ZBROJI_PERIPH_BUS_if
// Bindable checker with concise but thorough protocol and register-behavior checks.

module zbroji_HLS_ZBROJI_PERIPH_BUS_if_sva
#(parameter int C_ADDR_WIDTH = 6,
  parameter int C_DATA_WIDTH = 32,
  // Mirror address map (defaults match DUT)
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_AP_CTRL     = 6'h00,
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_GIE         = 6'h04,
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_IER         = 6'h08,
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_ISR         = 6'h0c,
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_A_CTRL      = 6'h10,
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_A_DATA_0    = 6'h14,
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_B_CTRL      = 6'h18,
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_B_DATA_0    = 6'h1c,
  parameter logic [C_ADDR_WIDTH-1:0] ADDR_AP_RETURN_0 = 6'h20,
  // FSM encodings
  parameter logic [1:0] WRIDLE = 2'd0,
  parameter logic [1:0] WRDATA = 2'd1,
  parameter logic [1:0] WRRESP = 2'd2,
  parameter logic [1:0] RDIDLE = 2'd0,
  parameter logic [1:0] RDDATA = 2'd1
)(
  input  logic                      ACLK,
  input  logic                      ARESETN,
  input  logic [C_ADDR_WIDTH-1:0]   AWADDR,
  input  logic                      AWVALID,
  input  logic                      AWREADY,
  input  logic [C_DATA_WIDTH-1:0]   WDATA,
  input  logic [C_DATA_WIDTH/8-1:0] WSTRB,
  input  logic                      WVALID,
  input  logic                      WREADY,
  input  logic [1:0]                BRESP,
  input  logic                      BVALID,
  input  logic                      BREADY,
  input  logic [C_ADDR_WIDTH-1:0]   ARADDR,
  input  logic                      ARVALID,
  input  logic                      ARREADY,
  input  logic [C_DATA_WIDTH-1:0]   RDATA,
  input  logic [1:0]                RRESP,
  input  logic                      RVALID,
  input  logic                      RREADY,
  input  logic                      interrupt,
  input  logic [31:0]               I_a,
  input  logic [31:0]               I_b,
  input  logic                      I_ap_start,
  input  logic                      O_ap_ready,
  input  logic                      O_ap_done,
  input  logic                      O_ap_idle,
  input  logic [31:0]               O_ap_return,

  // Internal DUT signals (bound hierarchically)
  input  logic [1:0]                wstate,
  input  logic [1:0]                rstate,
  input  logic [C_ADDR_WIDTH-1:0]   waddr,
  input  logic [31:0]               rdata,
  input  logic [31:0]               wmask,
  input  logic                      ap_done,
  input  logic                      ap_start,
  input  logic                      auto_restart,
  input  logic                      gie,
  input  logic                      ier,
  input  logic                      isr,
  input  logic [31:0]               _a,
  input  logic [31:0]               _b
);

  localparam int ADDR_BITS = C_ADDR_WIDTH;

  // Default clocking/reset
  default clocking cb @(posedge ACLK); endclocking
  default disable iff (!ARESETN);

  // Handshakes (derived)
  wire aw_hs = AWVALID & AWREADY;
  wire w_hs  = WVALID  & WREADY;
  wire b_hs  = BVALID  & BREADY;
  wire ar_hs = ARVALID & ARREADY;
  wire r_hs  = RVALID  & RREADY;

  // Mask recompute
  function automatic logic [31:0] wmask_calc (input logic [3:0] s);
    return {{8{s[3]}},{8{s[2]}},{8{s[1]}},{8{s[0]}}};
  endfunction

  // Reset effects
  assert property (@(posedge ACLK) !ARESETN |-> (wstate==WRIDLE && rstate==RDIDLE &&
                                                AWREADY && ARREADY &&
                                                !WREADY && !BVALID && !RVALID &&
                                                !ap_start && !ap_done &&
                                                !auto_restart && !gie && !ier && !isr));

  // FSM/output mapping
  assert property (AWREADY == (wstate==WRIDLE));
  assert property (WREADY  == (wstate==WRDATA));
  assert property (BVALID  == (wstate==WRRESP));
  assert property (ARREADY == (rstate==RDIDLE));
  assert property (RVALID  == (rstate==RDDATA));

  // Write FSM transitions
  assert property (wstate==WRIDLE && AWVALID |=> wstate==WRDATA);
  assert property (wstate==WRIDLE && !AWVALID |=> wstate==WRIDLE);
  assert property (wstate==WRDATA && WVALID |=> wstate==WRRESP);
  assert property (wstate==WRDATA && !WVALID |=> wstate==WRDATA);
  assert property (wstate==WRRESP && BREADY |=> wstate==WRIDLE);
  assert property (wstate==WRRESP && !BREADY |=> wstate==WRRESP);

  // Read FSM transitions
  assert property (rstate==RDIDLE && ARVALID |=> rstate==RDDATA);
  assert property (rstate==RDIDLE && !ARVALID |=> rstate==RDIDLE);
  assert property (rstate==RDDATA && RREADY |=> rstate==RDIDLE);
  assert property (rstate==RDDATA && !RREADY |=> rstate==RDDATA);

  // Protocol flow/liveness (bounded by environment progress via until_with)
  assert property (aw_hs |=> (!AWREADY && WREADY) until_with w_hs);
  assert property (w_hs  |=> (BVALID && !AWREADY && !WREADY) until_with b_hs);
  assert property (b_hs  |=> AWREADY);
  assert property (ar_hs |=> (RVALID && !ARREADY) until_with r_hs);
  assert property (r_hs  |=> ARREADY);

  // RESP/signal stability
  assert property (BVALID |-> (BRESP==2'b00));
  assert property (RVALID |-> (RRESP==2'b00));
  assert property (RVALID && !RREADY |-> $stable(RDATA));

  // Address capture and stability
  assert property (aw_hs |=> waddr == $past(AWADDR[ADDR_BITS-1:0]));
  assert property (ARESETN && !aw_hs |-> $stable(waddr));

  // wmask correctness
  assert property (wmask == wmask_calc(WSTRB));

  // Register write effects (A and B) with byte-enable mask
  assert property ( (w_hs && waddr==ADDR_A_DATA_0)
                    |=> I_a == ((WDATA & wmask_calc(WSTRB)) | ($past(I_a) & ~wmask_calc(WSTRB))) );
  assert property ( (w_hs && waddr==ADDR_B_DATA_0)
                    |=> I_b == ((WDATA & wmask_calc(WSTRB)) | ($past(I_b) & ~wmask_calc(WSTRB))) );

  // AP control: ap_start generation and pulse behavior
  assert property ( ap_start |-> ((w_hs && waddr==ADDR_AP_CTRL && WSTRB[0] && WDATA[0]) ||
                                  (O_ap_done && auto_restart)) );
  assert property ( ap_start && !((w_hs && waddr==ADDR_AP_CTRL && WSTRB[0] && WDATA[0]) ||
                                  (O_ap_done && auto_restart)) |=> !ap_start );

  // ap_done set/clear behavior
  assert property ($rose(ap_done) |-> O_ap_done);
  assert property (ap_done && !(ar_hs && (ARADDR[ADDR_BITS-1:0]==ADDR_AP_CTRL)) && !O_ap_done |=> ap_done);

  // auto_restart update
  assert property ( (w_hs && waddr==ADDR_AP_CTRL && WSTRB[0]) |=> auto_restart == WDATA[7] );
  assert property ( ARESETN && !(w_hs && waddr==ADDR_AP_CTRL && WSTRB[0]) |-> $stable(auto_restart) );

  // GIE/IER write behavior and stability
  assert property ( (w_hs && waddr==ADDR_GIE && WSTRB[0]) |=> gie == WDATA[0] );
  assert property ( ARESETN && !(w_hs && waddr==ADDR_GIE && WSTRB[0]) |-> $stable(gie) );

  assert property ( (w_hs && waddr==ADDR_IER && WSTRB[0]) |=> ier == WDATA[0] );
  assert property ( ARESETN && !(w_hs && waddr==ADDR_IER && WSTRB[0]) |-> $stable(ier) );

  // ISR set/toggle semantics
  assert property ( (w_hs && waddr==ADDR_ISR && WSTRB[0]) |=> isr == ($past(isr) ^ WDATA[0]) );
  assert property ( $rose(isr) |-> (ier && O_ap_done) || (w_hs && waddr==ADDR_ISR && WSTRB[0] && ($past(isr)==1'b0) && (WDATA[0]==1'b1)) );
  assert property ( $fell(isr) |-> (w_hs && waddr==ADDR_ISR && WSTRB[0] && ($past(isr)==1'b1) && (WDATA[0]==1'b1)) );

  // Interrupt decode
  assert property (interrupt == (gie & isr));

  // Read data correctness (sampled on ar_hs, observed on next cycle with RVALID)
  // AP_CTRL fields we can observe via ports
  assert property ( ar_hs && (ARADDR[ADDR_BITS-1:0]==ADDR_AP_CTRL)
                    |=> (RVALID && RDATA[0]==$past(I_ap_start) &&
                         RDATA[2]==$past(O_ap_idle) &&
                         RDATA[3]==$past(O_ap_ready)) );
  // A/B/RETURN registers
  assert property ( ar_hs && (ARADDR[ADDR_BITS-1:0]==ADDR_A_DATA_0)
                    |=> (RVALID && RDATA==$past(_a)) );
  assert property ( ar_hs && (ARADDR[ADDR_BITS-1:0]==ADDR_B_DATA_0)
                    |=> (RVALID && RDATA==$past(_b)) );
  assert property ( ar_hs && (ARADDR[ADDR_BITS-1:0]==ADDR_AP_RETURN_0)
                    |=> (RVALID && RDATA==$past(O_ap_return)) );

  // Coverage
  cover property (aw_hs ##[1:8] w_hs ##[1:8] b_hs);
  cover property (ar_hs ##1 RVALID ##[1:8] r_hs);
  cover property (w_hs && waddr==ADDR_AP_CTRL && WSTRB[0] && WDATA[0] ##1 ap_start);
  cover property ((w_hs && waddr==ADDR_AP_CTRL && WSTRB[0] && WDATA[7]) ##[1:20] (O_ap_done && auto_restart) ##1 ap_start);
  cover property (O_ap_done ##1 ap_done ##[1:8] (ar_hs && (ARADDR[ADDR_BITS-1:0]==ADDR_AP_CTRL)) ##1 !ap_done);
  cover property (ier && O_ap_done ##1 isr ##[1:8] (w_hs && waddr==ADDR_ISR && WSTRB[0] && (WDATA[0]==1)) ##1 !isr);
  cover property (w_hs && waddr==ADDR_A_DATA_0 && (WSTRB!=4'hF));
  cover property (interrupt);
endmodule

// Bind into the DUT (tool may require this in a separate file)
bind zbroji_HLS_ZBROJI_PERIPH_BUS_if
  zbroji_HLS_ZBROJI_PERIPH_BUS_if_sva
  #(.C_ADDR_WIDTH(C_ADDR_WIDTH),
    .C_DATA_WIDTH(C_DATA_WIDTH))
  zbroji_HLS_ZBROJI_PERIPH_BUS_if_sva_i
  (.*,
   .wstate(wstate),
   .rstate(rstate),
   .waddr(waddr),
   .rdata(rdata),
   .wmask(wmask),
   .ap_done(ap_done),
   .ap_start(ap_start),
   .auto_restart(auto_restart),
   .gie(gie),
   .ier(ier),
   .isr(isr),
   ._a(_a),
   ._b(_b));