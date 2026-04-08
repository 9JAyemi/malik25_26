module arithmetic_assertions (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [2:0] ctrl,
    input logic [7:0] z
);

    // ctrl=000 selects the 8-bit sum.
    check_ctrl_sum: assert property (
        @(posedge clk) (ctrl == 3'b000) |-> (z == (a + b))
    );

    // ctrl=001 selects the 8-bit difference.
    check_ctrl_difference: assert property (
        @(posedge clk) (ctrl == 3'b001) |-> (z == (a - b))
    );

    // ctrl=010 selects the low 8 bits of the product.
    check_ctrl_product_low_byte: assert property (
        @(posedge clk) (ctrl == 3'b010) |-> ({8'h00, z} == ((a * b) & 16'h00FF))
    );

    // ctrl=011 selects the quotient when the divisor is nonzero.
    check_ctrl_quotient: assert property (
        @(posedge clk) ((ctrl == 3'b011) && (b != 8'h00)) |-> (z == (a / b))
    );

    // ctrl=100 selects the remainder when the divisor is nonzero.
    check_ctrl_remainder: assert property (
        @(posedge clk) ((ctrl == 3'b100) && (b != 8'h00)) |-> (z == (a % b))
    );

    // ctrl=101 selects bitwise AND.
    check_ctrl_and: assert property (
        @(posedge clk) (ctrl == 3'b101) |-> (z == (a & b))
    );

    // ctrl=110 selects bitwise OR.
    check_ctrl_or: assert property (
        @(posedge clk) (ctrl == 3'b110) |-> (z == (a | b))
    );

    // ctrl=111 selects bitwise XOR.
    check_ctrl_xor: assert property (
        @(posedge clk) (ctrl == 3'b111) |-> (z == (a ^ b))
    );

endmodule