module calculator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] add,
    input logic [3:0] sub,
    input logic [3:0] mul,
    input logic [3:0] div
);

    // add reflects the 4-bit sum of A and B.
    check_add_matches_sum: assert property (
        @(posedge clk) add == ((A + B) & 4'hF)
    );

    // sub reflects the 4-bit difference of A and B.
    check_sub_matches_difference: assert property (
        @(posedge clk) sub == ((A - B) & 4'hF)
    );

    // mul reflects the low 4 bits of the product.
    check_mul_matches_product_low_bits: assert property (
        @(posedge clk) mul == ((A * B) & 4'hF)
    );

    // div reflects the quotient when the divisor is nonzero.
    check_div_matches_quotient: assert property (
        @(posedge clk) (B != 4'd0) |-> (div == (A / B))
    );

    // adding zero leaves A unchanged.
    check_add_zero_identity: assert property (
        @(posedge clk) (B == 4'd0) |-> (add == A)
    );

    // subtracting zero leaves A unchanged.
    check_sub_zero_identity: assert property (
        @(posedge clk) (B == 4'd0) |-> (sub == A)
    );

    // equal operands subtract to zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) (A == B) |-> (sub == 4'd0)
    );

    // any zero operand forces the product to zero.
    check_mul_zero_operand_zero: assert property (
        @(posedge clk) ((A == 4'd0) || (B == 4'd0)) |-> (mul == 4'd0)
    );

    // dividing by one leaves A unchanged.
    check_div_by_one_identity: assert property (
        @(posedge clk) (B == 4'd1) |-> (div == A)
    );

    // a smaller nonzero numerator divides down to zero.
    check_div_smaller_numerator_zero: assert property (
        @(posedge clk) ((B != 4'd0) && (A < B)) |-> (div == 4'd0)
    );

endmodule