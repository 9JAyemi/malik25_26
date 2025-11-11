
module wishbone_buf (
    input i_clk,
    input i_req,
    input i_write,
    input [127:0] i_wdata,
    input [15:0] i_be,
    input [31:0] i_addr,
    output [127:0] o_rdata,
    output o_ack,
    output o_valid,
    input i_accepted,
    output o_write,
    output [127:0] o_wdata,
    output [15:0] o_be,
    output [31:0] o_addr,
    input [127:0] i_rdata,
    input i_rdata_valid
);

reg [1:0] wbuf_used_r = 2'd0;
reg [31:0] wbuf_addr_r0;
reg [31:0] wbuf_addr_r1;
reg [127:0] wbuf_wdata_r0;
reg [127:0] wbuf_wdata_r1;
reg [15:0] wbuf_be_r0;
reg [15:0] wbuf_be_r1;
reg [1:0] wbuf_write_r = 2'd0;
reg wbuf_wp_r = 1'd0;
reg wbuf_rp_r = 1'd0;
reg busy_reading_r = 1'd0;
reg wait_rdata_valid_r = 1'd0;
reg ack_owed_r = 1'd0;
wire in_wreq;

assign in_wreq = i_req && i_write;

always @(posedge i_clk) begin
    if ((in_wreq && !busy_reading_r) && ((wbuf_used_r == 2'd1) || (wbuf_used_r == 2'd0 && !i_accepted))) begin
        wbuf_used_r <= wbuf_used_r + 1'd1;
    end else if (o_valid && i_accepted && (wbuf_used_r != 2'd0)) begin
        wbuf_used_r <= wbuf_used_r - 1'd1;
    end
end

always @(posedge i_clk) begin
    if (in_wreq) begin
        ack_owed_r <= 1'd1;
    end else if (!i_req && o_ack) begin
        ack_owed_r <= 1'd0;
    end
end

always @(posedge i_clk) begin
    if (in_wreq && !o_ack) begin
        if (wbuf_wp_r == 1'd0) begin
            wbuf_wdata_r0 <= i_wdata;
            wbuf_addr_r0 <= i_addr;
            wbuf_be_r0 <= i_write ? i_be : 16'hffff;
            wbuf_write_r[0] <= i_write;
        end else if (wbuf_wp_r == 1'd1) begin
            wbuf_wdata_r1 <= i_wdata;
            wbuf_addr_r1 <= i_addr;
            wbuf_be_r1 <= i_write ? i_be : 16'hffff;
            wbuf_write_r[1] <= i_write;
        end
        wbuf_wp_r <= !wbuf_wp_r;
    end
end

always @(posedge i_clk) begin
    if (o_valid && i_accepted && (wbuf_used_r != 2'd0)) begin
        wbuf_rp_r <= !wbuf_rp_r;
    end
end

assign o_wdata = (wbuf_used_r != 2'd0) ? (wbuf_rp_r == 1'd0 ? wbuf_wdata_r0 : wbuf_wdata_r1 ) : i_wdata;
assign o_write = (wbuf_used_r != 2'd0) ? (wbuf_rp_r == 1'd0 ? wbuf_write_r[0] : wbuf_write_r[1]) : i_write;
assign o_addr = (wbuf_used_r != 2'd0) ? (wbuf_rp_r == 1'd0 ? wbuf_addr_r0 : wbuf_addr_r1 ) : i_addr;
assign o_be = (wbuf_used_r != 2'd0) ? (wbuf_rp_r == 1'd0 ? wbuf_be_r0 : wbuf_be_r1) : i_write ? i_be : 16'hffff;
assign o_ack = (in_wreq ? (wbuf_used_r == 2'd0) : i_rdata_valid) || (ack_owed_r && o_valid && i_accepted && (wbuf_used_r != 2'd0));
assign o_valid = (wbuf_used_r != 2'd0 || i_req) && !wait_rdata_valid_r;
assign o_rdata = i_rdata;

always @(posedge i_clk) begin
    if (o_valid && !o_write) begin
        busy_reading_r <= 1'd1;
    end else if (i_rdata_valid) begin
        busy_reading_r <= 1'd0;
    end
end

always @(posedge i_clk) begin
    if (o_valid && !o_write && i_accepted) begin
        wait_rdata_valid_r <= 1'd1;
    end else if (i_rdata_valid) begin
        wait_rdata_valid_r <= 1'd0;
    end
end

endmodule