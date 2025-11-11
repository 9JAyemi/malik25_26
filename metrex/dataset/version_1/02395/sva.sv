// SVA for adder_AXI_CTRL_s_axi
// Bind this module to the DUT:
// bind adder_AXI_CTRL_s_axi adder_AXI_CTRL_s_axi_sva #(.C_ADDR_WIDTH(C_ADDR_WIDTH), .C_DATA_WIDTH(C_DATA_WIDTH)) sva (.*);

module adder_AXI_CTRL_s_axi_sva #(
  parameter C_ADDR_WIDTH = 6,
  parameter C_DATA_WIDTH = 32
)(
  input  wire                      ACLK,
  input  wire                      ARESET,
  input  wire                      ACLK_EN,
  input  wire [C_ADDR_WIDTH-1:0]   AWADDR,
  input  wire                      AWVALID,
  input  wire                      AWREADY,
  input  wire [C_DATA_WIDTH-1:0]   WDATA,
  input  wire [C_DATA_WIDTH/8-1:0] WSTRB,
  input  wire                      WVALID,
  input  wire                      WREADY,
  input  wire [1:0]                BRESP,
  input  wire                      BVALID,
  input  wire                      BREADY,
  input  wire [C_ADDR_WIDTH-1:0]   ARADDR,
  input  wire                      ARVALID,
  input  wire                      ARREADY,
  input  wire [C_DATA_WIDTH-1:0]   RDATA,
  input  wire [1:0]                RRESP,
  input  wire                      RVALID,
  input  wire                      RREADY,
  input  wire                      interrupt,
  input  wire                      ap_start,
  input  wire                      ap_done,
  input  wire                      ap_ready,
  input  wire                      ap_idle,
  input  wire [31:0]               a,
  input  wire [31:0]               b,
  input  wire [31:0]               c,
  input  wire                      c_ap_vld
);

  // Address map (must match DUT)
  localparam [C_ADDR_WIDTH-1:0]
    ADDR_AP_CTRL  = 6'h00,
    ADDR_GIE      = 6'h04,
    ADDR_IER      = 6'h08,
    ADDR_ISR      = 6'h0c,
    ADDR_A_DATA_0 = 6'h10,
    ADDR_A_CTRL   = 6'h14,
    ADDR_B_DATA_0 = 6'h18,
    ADDR_B_CTRL   = 6'h1c,
    ADDR_C_DATA_0 = 6'h20,
    ADDR_C_CTRL   = 6'h24;

  // Local reconstructions
  wire aw_hs = AWVALID & AWREADY;
  wire w_hs  = WVALID  & WREADY;
  wire ar_hs = ARVALID & ARREADY;

  // Byte mask derived from WSTRB (32b)
  wire [31:0] wmask = {{8{WSTRB[3]}}, {8{WSTRB[2]}}, {8{WSTRB[1]}}, {8{WSTRB[0]}}};

  // Simple mirrors for readable/writable CSRs to check readback/interrupt
  logic gie_m, ier_m, isr_m, ar_m;
  logic [31:0] c_m;

  // Mirrors update
  always @(posedge ACLK) begin
    if (ARESET) begin
      gie_m <= 1'b0;
      ier_m <= 1'b0;
      isr_m <= 1'b0;
      ar_m  <= 1'b0;
      c_m   <= 32'h0;
    end else if (ACLK_EN) begin
      // GIE write/read mirror
      if (w_hs && (AWADDR[ C_ADDR_WIDTH-1:0 ] == ADDR_GIE) && WSTRB[0]) gie_m <= WDATA[0];
      // IER write/read mirror
      if (w_hs && (AWADDR[ C_ADDR_WIDTH-1:0 ] == ADDR_IER) && WSTRB[0]) ier_m <= WDATA[0];
      // ISR W1T (XOR) mirror: set on (ier_m & ap_done), toggle on write data[0]
      if (ier_m & ap_done) isr_m <= 1'b1;
      else if (w_hs && (AWADDR[ C_ADDR_WIDTH-1:0 ] == ADDR_ISR) && WSTRB[0]) isr_m <= isr_m ^ WDATA[0];
      // Auto-restart bit mirror in AP_CTRL[7]
      if (w_hs && (AWADDR[ C_ADDR_WIDTH-1:0 ] == ADDR_AP_CTRL) && WSTRB[0]) ar_m <= WDATA[7];
      // Capture c on valid
      if (c_ap_vld) c_m <= c;
    end
  end

  // Default clock/disables for assertions
  default clocking cb @(posedge ACLK); endclocking
  default disable iff (ARESET);

  // AXI-Lite: static response OKAY
  assert property (BRESP == 2'b00);
  assert property (RRESP == 2'b00);

  // AXI-Lite: channel exclusivity patterns (no two ready/valid of same write FSM phase at once)
  assert property (AWREADY |-> !WREADY && !BVALID);
  assert property (WREADY  |-> !AWREADY && !BVALID);
  assert property (BVALID  |-> !AWREADY && !WREADY);
  assert property (RVALID  |-> !ARREADY);

  // AXI-Lite: progress with ACLK_EN gating
  assert property (ACLK_EN && aw_hs |=> WREADY);                 // move to WRDATA -> WREADY high
  assert property (ACLK_EN && w_hs  |=> BVALID);                 // move to WRRESP -> BVALID high
  assert property (BVALID && !BREADY |=> BVALID);                // hold until BREADY
  assert property (ACLK_EN && ar_hs |=> RVALID);                 // move to RDDATA -> RVALID high
  assert property (RVALID && !RREADY |=> RVALID);                // hold until RREADY

  // Outputs stable when clocks disabled
  assert property (!ACLK_EN |-> $stable({AWREADY,WREADY,BVALID,ARREADY,RVALID,RDATA,interrupt,ap_start,a,b}));

  // Readback checks: GIE/IER/ISR
  assert property (ACLK_EN && ar_hs && (ARADDR == ADDR_GIE) |=> (RVALID && RDATA[0] == gie_m && RDATA[31:1] == '0));
  assert property (ACLK_EN && ar_hs && (ARADDR == ADDR_IER) |=> (RVALID && RDATA[0] == ier_m && RDATA[31:1] == '0));
  assert property (ACLK_EN && ar_hs && (ARADDR == ADDR_ISR) |=> (RVALID && RDATA[0] == isr_m && RDATA[31:1] == '0));

  // Interrupt equals GIE & ISR
  assert property (interrupt == (gie_m & isr_m));

  // AP_CTRL readback of visible bits
  assert property (ACLK_EN && ar_hs && (ARADDR == ADDR_AP_CTRL) |=> (RVALID &&
                                                                     RDATA[0] == ap_start &&
                                                                     RDATA[2] == ap_idle  &&
                                                                     RDATA[3] == ap_ready));

  // AP_CTRL[7] auto-restart: write-read coherence (until next write)
  property p_apctrl_ar_readback;
    (ACLK_EN && w_hs && (AWADDR == ADDR_AP_CTRL) && WSTRB[0]) |-> ##1
      (! (ACLK_EN && w_hs && (AWADDR == ADDR_AP_CTRL) && WSTRB[0]))
      [*0:$] ##1 (ACLK_EN && ar_hs && (ARADDR == ADDR_AP_CTRL)) |=> (RVALID && RDATA[7] == $past(WDATA[7], 1));
  endproperty
  assert property (p_apctrl_ar_readback);

  // ap_start only asserted when triggered by SW start write or auto-restart+ap_done
  assert property (ap_start |-> ((ACLK_EN && w_hs && (AWADDR == ADDR_AP_CTRL) && WSTRB[0] && WDATA[0]) ||
                                 (ap_done && ar_m)));

  // A/B register masked write behavior to output ports
  assert property (ACLK_EN && w_hs && (AWADDR == ADDR_A_DATA_0)
                   |=> a == (($past(WDATA) & $past(wmask)) | ($past(a) & ~$past(wmask))));
  assert property (ACLK_EN && w_hs && (AWADDR == ADDR_B_DATA_0)
                   |=> b == (($past(WDATA) & $past(wmask)) | ($past(b) & ~$past(wmask))));

  // Readback of A/B/C data windows
  assert property (ACLK_EN && ar_hs && (ARADDR == ADDR_A_DATA_0) |=> (RVALID && RDATA == a));
  assert property (ACLK_EN && ar_hs && (ARADDR == ADDR_B_DATA_0) |=> (RVALID && RDATA == b));
  assert property (ACLK_EN && ar_hs && (ARADDR == ADDR_C_DATA_0) |=> (RVALID && RDATA == c_m));

  // C status sticky bit: set on c_ap_vld, clear on read of C_CTRL
  // First read after c_ap_vld must return bit0=1
  assert property (ACLK_EN && c_ap_vld |-> ##[1:$] (ACLK_EN && ar_hs && (ARADDR == ADDR_C_CTRL)) |=> (RVALID && RDATA[0] == 1'b1));
  // Subsequent read without new c_ap_vld must return 0
  property p_cctrl_clear_on_read;
    (ACLK_EN && ar_hs && (ARADDR == ADDR_C_CTRL)) |=> (RVALID && RDATA[0] == 1'b1) ##1
      (! (ACLK_EN && c_ap_vld))[*0:$] ##1
      (ACLK_EN && ar_hs && (ARADDR == ADDR_C_CTRL)) |=> (RVALID && RDATA[0] == 1'b0);
  endproperty
  assert property (p_cctrl_clear_on_read);

  // ISR W1T semantics mirrored and readback
  // Write 1 toggles (clears when 1), write 0 holds
  assert property (ACLK_EN && w_hs && (AWADDR == ADDR_ISR) && WSTRB[0] && (WDATA[0] == 1'b0) |=> isr_m == $past(isr_m));
  assert property (ACLK_EN && w_hs && (AWADDR == ADDR_ISR) && WSTRB[0] && (WDATA[0] == 1'b1) |=> isr_m == ~$past(isr_m));

  // Basic coverage

  // One complete write transaction
  cover property (ACLK_EN && aw_hs ##1 WREADY ##0 WVALID ##1 BVALID ##0 BREADY);

  // One complete read transaction
  cover property (ACLK_EN && ar_hs ##1 RVALID ##0 RREADY);

  // Cover writes to each key address
  cover property (ACLK_EN && w_hs && (AWADDR == ADDR_AP_CTRL));
  cover property (ACLK_EN && w_hs && (AWADDR == ADDR_GIE));
  cover property (ACLK_EN && w_hs && (AWADDR == ADDR_IER));
  cover property (ACLK_EN && w_hs && (AWADDR == ADDR_ISR));
  cover property (ACLK_EN && w_hs && (AWADDR == ADDR_A_DATA_0));
  cover property (ACLK_EN && w_hs && (AWADDR == ADDR_B_DATA_0));

  // Cover auto-restart path: set AR, see ap_done cause ap_start
  cover property (ACLK_EN && w_hs && (AWADDR == ADDR_AP_CTRL) && WSTRB[0] && WDATA[7] ##[1:$]
                  ap_done && ap_start);

  // Cover c_ap_vld set and clear-by-read
  cover property (ACLK_EN && c_ap_vld ##[1:$] (ACLK_EN && ar_hs && (ARADDR == ADDR_C_CTRL)) ##1 RVALID && RDATA[0]);

  // Cover interrupt assertion and clear through ISR write-1
  cover property (ACLK_EN && w_hs && (AWADDR == ADDR_GIE) && WSTRB[0] && WDATA[0] ##[1:$]
                  (ACLK_EN && w_hs && (AWADDR == ADDR_IER) && WSTRB[0] && WDATA[0]) ##[1:$]
                  ap_done ##0 interrupt ##[1:$]
                  (ACLK_EN && w_hs && (AWADDR == ADDR_ISR) && WSTRB[0] && WDATA[0]) ##1 !interrupt);

endmodule