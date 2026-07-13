
module signed_multiplier_32 (
    clk,
    reset,
    ce,
    din0,
    din1,
    dout
);

parameter ID = 32'd1;
parameter NUM_STAGE = 32'd1;
parameter din0_WIDTH = 32'd1;
parameter din1_WIDTH = 32'd1;
parameter dout_WIDTH = 32'd1;

input clk;
input reset;
input ce;
input signed [din0_WIDTH - 1:0] din0;
input signed [din1_WIDTH - 1:0] din1;
output signed [dout_WIDTH + din0_WIDTH - 1:0] dout;

wire [2*dout_WIDTH-1:0] mul_result;
reg signed [dout_WIDTH-1:0] dout_int;

assign dout = dout_int;

always @ (posedge clk, posedge reset) begin
    if (reset) begin
        dout_int <= 0;
    end else begin
        if (ce) begin
            dout_int <= mul_result[2*dout_WIDTH-1:dout_WIDTH];
        end
    end
end

signed_multiplier multiplier_0_U (
    .clk( clk ),
    .ce( ce ),
    .a( din0 ),
    .b( din1 ),
    .p( mul_result ));

endmodule

module signed_multiplier (
    clk,
    ce,
    a,
    b,
    p
);

parameter ID = 32'd1;
parameter NUM_STAGE = 32'd1;
parameter din0_WIDTH = 32'd1;
parameter din1_WIDTH = 32'd1;
parameter dout_WIDTH = 32'd1;

input clk;
input ce;
input signed [din0_WIDTH - 1:0] a;
input signed [din1_WIDTH - 1:0] b;
output signed [2*dout_WIDTH-1:0] p;

wire [2*dout_WIDTH-1:0] mul_result;

multiply multiplier_U (
    .clk( clk ),
    .ce( ce ),
    .a( a ),
    .b( b ),
    .p( mul_result ));

assign p = mul_result;

endmodule

module multiply (
    clk,
    ce,
    a,
    b,
    p
);

parameter ID = 32'd1;
parameter NUM_STAGE = 32'd1;
parameter din0_WIDTH = 32'd1;
parameter din1_WIDTH = 32'd1;
parameter dout_WIDTH = 32'd1;

input clk;
input ce;
input signed [din0_WIDTH - 1:0] a;
input signed [din1_WIDTH - 1:0] b;
output signed [2*dout_WIDTH-1:0] p;

wire signed [din0_WIDTH - 1:0] a_temp;
wire signed [din1_WIDTH - 1:0] b_temp;
wire signed [2*dout_WIDTH-1:0] p_temp;

assign a_temp = a;
assign b_temp = b;
assign p_temp = a_temp * b_temp;

assign p = p_temp;

endmodule
