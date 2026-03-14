
module multiplier (
    input [3:0] a,
    input [3:0] b,
    output [7:0] product
);

reg [3:0] a_reg, b_reg;
reg [7:0] product_reg;

always @(*) begin
    a_reg = a;
    b_reg = b;
    product_reg = a_reg * b_reg;
end

assign product = product_reg;

endmodule
