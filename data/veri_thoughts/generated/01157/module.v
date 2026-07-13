
module top_module (
    input clk,
    input reset,
    input data,
    output reg q
);
reg [2:0] shift_reg;
wire [2:0] complement;

shift_register sr (.clk(clk), .reset(reset), .data(data), .q(shift_reg));
functional_module fm (.in1(shift_reg), .in2(q), .out(complement));
d_ff ff (.clk(clk), .reset(reset), .d(complement[2]), .q(q));
endmodule
module shift_register(
    input clk,
    input reset,
    input data,
    output reg [2:0] q
);
always @(posedge clk) begin
    if (reset) begin
        q <= 3'b0;
    end else begin
        q <= {q[1:0], data};
    end
end
endmodule
module d_ff (
    input clk,
    input reset,
    input d,
    output reg q
);
always @(posedge clk) begin
    if (reset) begin
        q <= 1'b0;
    end else begin
        q <= d;
    end
end
endmodule
module functional_module (
    input [2:0] in1,
    input in2,
    output reg [2:0] out
);
always@(*) begin
    out = ~in1;
end
endmodule