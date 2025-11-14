
module zbroji_HLS_ZBROJI_PERIPH_BUS_if
#(parameter
    C_ADDR_WIDTH = 6,
    C_DATA_WIDTH = 32
)(
    input  wire                      ACLK,
    input  wire                      ARESETN,
    input  wire [C_ADDR_WIDTH-1:0]   AWADDR,
    input  wire                      AWVALID,
    output wire                      AWREADY,
    input  wire [C_DATA_WIDTH-1:0]   WDATA,
    input  wire [C_DATA_WIDTH/8-1:0] WSTRB,
    input  wire                      WVALID,
    output wire                      WREADY,
    output wire [1:0]                BRESP,
    output wire                      BVALID,
    input  wire                      BREADY,
    input  wire [C_ADDR_WIDTH-1:0]   ARADDR,
    input  wire                      ARVALID,
    output wire                      ARREADY,
    output wire [C_DATA_WIDTH-1:0]   RDATA,
    output wire [1:0]                RRESP,
    output wire                      RVALID,
    input  wire                      RREADY,
    output wire                      interrupt,
    output wire [31:0]               I_a,
    output wire [31:0]               I_b,
    output wire                      I_ap_start,
    input  wire                      O_ap_ready,
    input  wire                      O_ap_done,
    input  wire                      O_ap_idle,
    input  wire [31:0]               O_ap_return
);
localparam
    ADDR_BITS = 6;

localparam
    ADDR_AP_CTRL     = 6'h00,
    ADDR_GIE         = 6'h04,
    ADDR_IER         = 6'h08,
    ADDR_ISR         = 6'h0c,
    ADDR_A_CTRL      = 6'h10,
    ADDR_A_DATA_0    = 6'h14,
    ADDR_B_CTRL      = 6'h18,
    ADDR_B_DATA_0    = 6'h1c,
    ADDR_AP_RETURN_0 = 6'h20;

localparam
    WRIDLE = 2'd0,
    WRDATA = 2'd1,
    WRRESP = 2'd2;

localparam
    RDIDLE = 2'd0,
    RDDATA = 2'd1;

reg  [1:0]           wstate;
reg  [1:0]           wnext;
reg  [ADDR_BITS-1:0] waddr;
wire [31:0]          wmask;
wire                 aw_hs;
wire                 w_hs;
reg  [1:0]           rstate;
reg  [1:0]           rnext;
reg  [31:0]          rdata;
wire                 ar_hs;
wire [ADDR_BITS-1:0] raddr;
wire                 ap_idle;
reg                  ap_done;
wire                 ap_ready;
reg                  ap_start;
reg                  auto_restart;
reg                  gie;
reg                  ier;
reg                  isr;
reg  [31:0]          _a;
reg  [31:0]          _b;
wire [31:0]          ap_return;

assign AWREADY = (wstate == WRIDLE);
assign WREADY  = (wstate == WRDATA);
assign BRESP   = 2'b00;  assign BVALID  = (wstate == WRRESP);
assign wmask   = { {8{WSTRB[3]}}, {8{WSTRB[2]}}, {8{WSTRB[1]}}, {8{WSTRB[0]}} };
assign aw_hs   = AWVALID & AWREADY;
assign w_hs    = WVALID & WREADY;

always @(posedge ACLK) begin
    if (~ARESETN)
        wstate <= WRIDLE;
    else
        wstate <= wnext;
end

always @(*) begin
    case (wstate)
        WRIDLE:
            if (AWVALID)
                wnext = WRDATA;
            else
                wnext = WRIDLE;
        WRDATA:
            if (WVALID)
                wnext = WRRESP;
            else
                wnext = WRDATA;
        WRRESP:
            if (BREADY)
                wnext = WRIDLE;
            else
                wnext = WRRESP;
        default:
            wnext = WRIDLE;
    endcase
end

always @(posedge ACLK) begin
    if (aw_hs)
        waddr <= AWADDR[ADDR_BITS-1:0];
end
assign ARREADY = (rstate == RDIDLE);
assign RDATA   = rdata;
assign RRESP   = 2'b00;  assign RVALID  = (rstate == RDDATA);
assign ar_hs   = ARVALID & ARREADY;
assign raddr   = ARADDR[ADDR_BITS-1:0];

always @(posedge ACLK) begin
    if (~ARESETN)
        rstate <= RDIDLE;
    else
        rstate <= rnext;
end

always @(*) begin
    case (rstate)
        RDIDLE:
            if (ARVALID)
                rnext = RDDATA;
            else
                rnext = RDIDLE;
        RDDATA:
            if (RREADY)
                rnext = RDIDLE;
            else
                rnext = RDDATA;
        default:
            rnext = RDIDLE;
    endcase
end

always @(posedge ACLK) begin
    if (ar_hs) begin
        rdata <= 1'b0;
        case (raddr)
            ADDR_AP_CTRL: begin
                rdata[0] <= ap_start;
                rdata[1] <= ap_done;
                rdata[2] <= ap_idle;
                rdata[3] <= ap_ready;
                rdata[7] <= auto_restart;
            end
            ADDR_GIE: begin
                rdata <= gie;
            end
            ADDR_IER: begin
                rdata <= ier;
            end
            ADDR_ISR: begin
                rdata <= isr;
            end
            ADDR_A_DATA_0: begin
                rdata <= _a[31:0];
            end
            ADDR_B_DATA_0: begin
                rdata <= _b[31:0];
            end
            ADDR_AP_RETURN_0: begin
                rdata <= ap_return[31:0];
            end
        endcase
    end
end
assign interrupt  = gie & (|isr);
assign I_ap_start = ap_start;
assign ap_idle    = O_ap_idle;
assign ap_ready   = O_ap_ready;
assign I_a        = _a;
assign I_b        = _b;
assign ap_return  = O_ap_return;

always @(posedge ACLK) begin
    if (~ARESETN)
        ap_start <= 1'b0;
    else if (w_hs && waddr == ADDR_AP_CTRL && WSTRB[0] && WDATA[0])
        ap_start <= 1'b1;
    else if (O_ap_done & auto_restart)
        ap_start <= 1'b1; else
        ap_start <= 1'b0; end

always @(posedge ACLK) begin
    if (~ARESETN)
        ap_done <= 1'b0;
    else if (O_ap_done)
        ap_done <= 1'b1;
    else if (ar_hs && raddr == ADDR_AP_CTRL)
        ap_done <= 1'b0; end

always @(posedge ACLK) begin
    if (~ARESETN)
        auto_restart <= 1'b0;
    else if (w_hs && waddr == ADDR_AP_CTRL && WSTRB[0])
        auto_restart <=  WDATA[7];
end

always @(posedge ACLK) begin
    if (~ARESETN)
        gie <= 1'b0;
    else if (w_hs && waddr == ADDR_GIE && WSTRB[0])
        gie <= WDATA[0];
end

always @(posedge ACLK) begin
    if (~ARESETN)
        ier <= 1'b0;
    else if (w_hs && waddr == ADDR_IER && WSTRB[0])
        ier <= WDATA[0];
end

always @(posedge ACLK) begin
    if (~ARESETN)
        isr <= 1'b0;
    else if (ier & O_ap_done)
        isr <= 1'b1;
    else if (w_hs && waddr == ADDR_ISR && WSTRB[0])
        isr <= isr ^ WDATA[0]; end

always @(posedge ACLK) begin
    if (w_hs && waddr == ADDR_A_DATA_0)
        _a[31:0] <= (WDATA[31:0] & wmask) | (_a[31:0] & ~wmask);
end

always @(posedge ACLK) begin
    if (w_hs && waddr == ADDR_B_DATA_0)
        _b[31:0] <= (WDATA[31:0] & wmask) | (_b[31:0] & ~wmask);
end

endmodule
