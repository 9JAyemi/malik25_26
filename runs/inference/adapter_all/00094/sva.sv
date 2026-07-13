module RippleAdder2_sva #(
    parameter int p_wordlength = 4
) (
    input logic        clk,
    input logic [3:0]  a,
    input logic [3:0]  b,
    input logic        ci,
    input logic        co,
    input logic [3:0]  s
);

    // Combinational DUT with no reset; sample on an external clock.

    // Full 5-bit result matches a + b + ci.
    check_full_addition: assert property (
        @(posedge clk) {co, s} == ({1'b0, a} + {1'b0, b} + ci)
    );

    // Carry-out is the MSB of the 5-bit sum.
    check_carry_out: assert property (
        @(posedge clk) co == (({1'b0, a} + {1'b0, b} + ci)[4])
    );

    // Sum bits match the low 4 bits of the 5-bit sum.
    check_sum_bits: assert property (
        @(posedge clk) s == (({1'b0, a} + {1'b0, b} + ci)[3:0])
    );

    // Adding zero on b with no carry-in passes a through unchanged.
    check_add_zero_b: assert property (
        @(posedge clk) (b == 4'h0 && ci == 1'b0) |-> (s == a && co == 1'b0)
    );

    // Adding zero on a with no carry-in passes b through unchanged.
    check_add_zero_a: assert property (
        @(posedge clk) (a == 4'h0 && ci == 1'b0) |-> (s == b && co == 1'b0)
    );

    // With a and b at zero, carry-in increments the result by one.
    check_increment_with_ci: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0) |-> (s == 4'h1 && co == 1'b0)
    );

    // With a and b at zero, no carry-in produces zero.
    check_zero_with_no_ci: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0 && ci == 1'b0) |-> (s == 4'h0 && co == 1'b0)
    );

    // With a and b at 4'hF, carry-in increments the result by one.
    check_max_with_ci: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF) |-> (s == 4'h0 && co == 1'b1)
    );

    // With a and b at 4'hF, no carry-in produces 4'hF with carry-out.
    check_max_with_no_ci: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && ci == 1'b0) |-> (s == 4'hF && co == 1'b1)
    );

    // Carry-out is high only when the 5-bit sum exceeds 4 bits.
    check_carry_overflow: assert property (
        @(posedge clk) co == (({1'b0, a} + {1'b0, b} + ci) >= 5'd16)
    );

    // Carry-out is low when the 5-bit sum fits in 4 bits.
    check_no_carry_overflow: assert property (
        @(posedge clk) co == (({1'b0, a} + {1'b0, b} + ci) < 5'd16)
    );

endmodule