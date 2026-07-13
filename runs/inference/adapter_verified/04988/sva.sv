module calculator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] add,
    input logic [3:0] sub,
    input logic [3:0] mul,
    input logic [3:0] div
);

// add is the 4-bit sum of A and B.
    check_add_result: assert property (
        @(posedge clk) add == (A + B)
    );

// sub is the 4-bit difference of A and B.
    check_sub_result: assert property (
        @(posedge clk) sub == (A - B)
    );

// mul is the 4-bit product of A and B.
    check_mul_result: assert property (
        @(posedge clk) mul == (A * B)
    );

// div is the 4-bit quotient of A divided by B.
    check_div_result: assert property (
        @(posedge clk) div == (A / B)
    );

endmodule
