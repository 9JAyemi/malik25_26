
module sirv_gnrl_cdc_rx
# (
  parameter DW = 32,
  parameter SYNC_DP = 2
) (
  // The 4-phases handshake interface at in-side
  //     There are 4 steps required for a full transaction. 
  //         (1) The i_vld is asserted high 
  //         (2) The i_rdy is asserted high
  //         (3) The i_vld is asserted low 
  //         (4) The i_rdy is asserted low
  input  i_vld_a, 
  output i_rdy, 
  input  [DW-1:0] i_dat,
  // The regular handshake interface at out-side
  //         Just the regular handshake o_vld & o_rdy like AXI
  output o_vld, 
  input  o_rdy, 
  output [DW-1:0] o_dat,

  input  clk,
  input  rst_n 
);

// Synchronize the asynchronous input signal
wire i_vld_sync;
sirv_gnrl_sync #(.DP(SYNC_DP), .DW(1)) u_i_vld_sync (
     .clk   (clk),
     .rst_n (rst_n),
     .din_a (i_vld_a),
     .dout  (i_vld_sync)
);

// D-type flip-flop to capture the synchronized input signal
reg i_vld_sync_r = 1'b0;
always @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        i_vld_sync_r <= 1'b0;
    end else begin
        i_vld_sync_r <= i_vld_sync;
    end
end

// Set or clear the input ready signal based on the synchronized input signal
wire buf_rdy;
reg i_rdy_r = 1'b0;
wire i_rdy_set = buf_rdy & i_vld_sync & (~i_rdy_r);
wire i_rdy_clr = ~i_vld_sync & i_vld_sync_r;
wire i_rdy_ena = i_rdy_set | i_rdy_clr;
wire i_rdy_nxt = i_rdy_set | (~i_rdy_clr);
always @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        i_rdy_r <= 1'b0;
    end else if (i_rdy_ena) begin
        i_rdy_r <= i_rdy_nxt;
    end
end
assign i_rdy = i_rdy_r;

// D-type flip-flop to capture the input data
reg [DW-1:0] buf_dat_r = {DW{1'b0}};
wire buf_dat_ena = i_rdy_set;
always @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        buf_dat_r <= {DW{1'b0}};
    end else if (buf_dat_ena) begin
        buf_dat_r <= i_dat;
    end
end

// Set or clear the buffer valid signal based on the output ready signal
reg buf_vld_r = 1'b0;
wire buf_vld_set = buf_dat_ena;
wire buf_vld_clr = o_vld & o_rdy;
wire buf_vld_ena = buf_vld_set | buf_vld_clr;
wire buf_vld_nxt = buf_vld_set | (~buf_vld_clr);
always @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        buf_vld_r <= 1'b0;
    end else if (buf_vld_ena) begin
        buf_vld_r <= buf_vld_nxt;
    end
end
assign buf_rdy = ~buf_vld_r;

// Output the buffer data
assign o_vld = buf_vld_r;
assign o_dat = buf_dat_r;

endmodule
module sirv_gnrl_sync
# (
  parameter DP = 1,
  parameter DW = 1
) (
  input  clk,
  input  rst_n,
  input  din_a,
  output dout
);

reg [DP*DW-1:0] sync_r = {DP*DW{1'b0}};

wire [DP*DW-1:0] sync_nxt;
genvar i;
for (i = 0; i < DP*DW; i = i + 1) begin
    if (i == 0)
        assign sync_nxt[i] = din_a;
    else
        assign sync_nxt[i] = sync_r[i-1] | (din_a & ~sync_r[i]);
end

always @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
        sync_r <= {DP*DW{1'b0}};
    end else begin
        sync_r <= sync_nxt;
    end
end

assign dout = sync_nxt[DP*DW-1];

endmodule