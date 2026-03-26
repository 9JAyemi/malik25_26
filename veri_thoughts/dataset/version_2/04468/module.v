
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input SUB,
    output [7:0] OUT
);

assign OUT = SUB ? (A - B) : (A + B);

endmodule

module multiplier (
    input [3:0] A,
    input [3:0] B,
    input clk,
    output [7:0] PRODUCT
);

wire [7:0] stage1_out;
wire [7:0] stage2_out;

adder_subtractor addsub1(.A(A), .B(B), .SUB(1'b0), .OUT(stage1_out));
adder_subtractor addsub2(.A(stage1_out[3:0]), .B(stage1_out[7:4]), .SUB(1'b0), .OUT(stage2_out));

reg [7:0] product_reg;

always @(posedge clk) begin
    product_reg <= stage2_out;
end

assign PRODUCT = product_reg;

endmodule
