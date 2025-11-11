
module adder_AXI_CTRL_s_axi
#(parameter
    C_ADDR_WIDTH = 6,
    C_DATA_WIDTH = 32
)(
    input  wire                      ACLK,
    input  wire                      ARESET,
    input  wire                      ACLK_EN,
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
    output wire                      ap_start,
    input  wire                      ap_done,
    input  wire                      ap_ready,
    input  wire                      ap_idle,
    output wire [31:0]               a,
    output wire [31:0]               b,
    input  wire [31:0]               c,
    input  wire                      c_ap_vld
);
localparam
    ADDR_BITS = 6;

localparam
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
wire                 int_ap_idle;
wire                 int_ap_ready;
reg                  int_ap_done;
reg                  int_ap_start;
reg                  int_auto_restart;
reg                  int_gie;
reg                  int_ier;
reg                  int_isr;
reg  [31:0]          int_a;
reg  [31:0]          int_b;
reg  [31:0]          int_c;
reg                  int_c_ap_vld;

assign AWREADY = (wstate == WRIDLE);
assign WREADY  = (wstate == WRDATA);
assign BRESP   = 2'b00;  assign BVALID  = (wstate == WRRESP);
assign wmask   = { {8{WSTRB[3]}}, {8{WSTRB[2]}}, {8{WSTRB[1]}}, {8{WSTRB[0]}} };
assign aw_hs   = AWVALID & AWREADY;
assign w_hs    = WVALID & WREADY;

always @(posedge ACLK) begin
    if (ACLK_EN) begin
        if (ARESET)
            wstate <= WRIDLE;
        else
            wstate <= wnext;
    end
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
    if (ACLK_EN) begin
        if (aw_hs)
            waddr <= AWADDR[ADDR_BITS-1:0];
    end
end
assign ARREADY = (rstate == RDIDLE);
assign RDATA   = rdata;
assign RRESP   = 2'b00;  assign RVALID  = (rstate == RDDATA);
assign ar_hs   = ARVALID & ARREADY;
assign raddr   = ARADDR[ADDR_BITS-1:0];

always @(posedge ACLK) begin
    if (ACLK_EN) begin
        if (ARESET)
            rstate <= RDIDLE;
        else
            rstate <= rnext;
    end
end

always @(*) begin
    case (rstate)
        RDIDLE:
            if (ARVALID)
                rnext = RDDATA;
            else
                rnext = RDIDLE;
        RDDATA:
            if (RREADY & RVALID)
                rnext = RDIDLE;
            else
                rnext = RDDATA;
        default:
            rnext = RDIDLE;
    endcase
end

always @(posedge ACLK) begin
    if (ACLK_EN) begin
        if (ar_hs) begin
            rdata <= 1'b0;
            case (raddr)
                ADDR_AP_CTRL: begin
                    rdata[0] <= int_ap_start;
                    rdata[1] <= int_ap_done;
                    rdata[2] <= int_ap_idle;
                    rdata[3] <= int_ap_ready;
                    rdata[7] <= int_auto_restart;
                end
                ADDR_GIE: begin
                    rdata <= int_gie;
                end
                ADDR_IER: begin
                    rdata <= int_ier;
                end
                ADDR_ISR: begin
                    rdata <= int_isr;
                end
                ADDR_A_DATA_0: begin
                    rdata <= int_a[31:0];
                end
                ADDR_B_DATA_0: begin
                    rdata <= int_b[31:0];
                end
                ADDR_C_DATA_0: begin
                    rdata <= int_c[31:0];
                end
                ADDR_C_CTRL: begin
                    rdata[0] <= int_c_ap_vld;
                end
            endcase
        end
    end
end
assign interrupt    = int_gie & (|int_isr);
assign ap_start     = int_ap_start;
assign int_ap_idle  = ap_idle;
assign int_ap_ready = ap_ready;
assign a            = int_a;
assign b            = int_b;

always @(posedge ACLK) begin
    if (ARESET)
        int_ap_start <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_AP_CTRL && WSTRB[0] && WDATA[0])
            int_ap_start <= 1'b1;
        else if (ap_done & int_auto_restart)
            int_ap_start <= 1'b1; else
            int_ap_start <= 1'b0; end
end

always @(posedge ACLK) begin
    if (ARESET)
        int_ap_done <= 1'b0;
    else if (ACLK_EN) begin
        if (ap_done)
            int_ap_done <= 1'b1;
        else if (ar_hs && raddr == ADDR_AP_CTRL)
            int_ap_done <= 1'b0; end
end

always @(posedge ACLK) begin
    if (ARESET)
        int_auto_restart <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_AP_CTRL && WSTRB[0])
            int_auto_restart <=  WDATA[7];
    end
end

always @(posedge ACLK) begin
    if (ARESET)
        int_gie <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_GIE && WSTRB[0])
            int_gie <= WDATA[0];
    end
end

always @(posedge ACLK) begin
    if (ARESET)
        int_ier <= 1'b0;
    else if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_IER && WSTRB[0])
            int_ier <= WDATA[0];
    end
end

always @(posedge ACLK) begin
    if (ARESET)
        int_isr <= 1'b0;
    else if (ACLK_EN) begin
        if (int_ier & ap_done)
            int_isr <= 1'b1;
        else if (w_hs && waddr == ADDR_ISR && WSTRB[0])
            int_isr <= int_isr ^ WDATA[0]; end
end

always @(posedge ACLK) begin
    if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_A_DATA_0)
            int_a[31:0] <= (WDATA[31:0] & wmask) | (int_a[31:0] & ~wmask);
    end
end

always @(posedge ACLK) begin
    if (ACLK_EN) begin
        if (w_hs && waddr == ADDR_B_DATA_0)
            int_b[31:0] <= (WDATA[31:0] & wmask) | (int_b[31:0] & ~wmask);
    end
end

always @(posedge ACLK) begin
    if (ARESET)
        int_c <= 0;
    else if (ACLK_EN) begin
        if (c_ap_vld)
            int_c <= c;
    end
end

always @(posedge ACLK) begin
    if (ARESET)
        int_c_ap_vld <= 1'b0;
    else if (ACLK_EN) begin
        if (c_ap_vld)
            int_c_ap_vld <= 1'b1;
        else if (ar_hs && raddr == ADDR_C_CTRL)
            int_c_ap_vld <= 1'b0; end
end

endmodule
