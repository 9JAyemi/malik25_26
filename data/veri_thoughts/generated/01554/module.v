module wb_mux(
    // Clock and reset
    clk, rst,

    // Internal i/f
    wb_freeze, rfwb_op,
    muxin_a, muxin_b, muxin_c, muxin_d,
    muxout, muxreg, muxreg_valid
);

parameter width = 32;


input               clk;
input               rst;

input               wb_freeze;
input   [2:0]       rfwb_op;
input   [width-1:0] muxin_a;
input   [width-1:0] muxin_b;
input   [width-1:0] muxin_c;
input   [width-1:0] muxin_d;
output  [width-1:0] muxout;
output  [width-1:0] muxreg;
output              muxreg_valid;

reg [width-1:0] muxout;
reg [width-1:0] muxreg;
reg muxreg_valid;

always @(posedge clk or posedge rst) begin
    if (rst) begin
        muxreg <= 32'd0;
        muxreg_valid <= 1'b0;
    end
    else if (!wb_freeze) begin
        muxreg <= muxout;
        muxreg_valid <= rfwb_op[0];
    end
end

always @(*) begin
    case(rfwb_op[2:1])
        2'b00: muxout = muxin_a;
        2'b01: muxout = muxin_b;
        2'b10: muxout = muxin_c;
        2'b11: muxout = muxin_d + 32'h8;
    endcase
end

endmodule