module half_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic sum,
    input logic carry_out
);

    // sum must equal A XOR B.
    check_sum_xor: assert property (
        @(posedge clk) sum == (A ^ B)
    );

    // carry_out must equal A AND B.
    check_carry_and: assert property (
        @(posedge clk) carry_out == (A & B)
    );

    // The two outputs must always be complementary.
    check_outputs_complementary: assert property (
        @(posedge clk) sum != carry_out
    );

    // Both inputs low must produce zero sum and zero carry.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B) |-> (!sum && !carry_out)
    );

    // A high and B low must produce sum high and carry low.
    check_a_high_b_low: assert property (
        @(posedge clk) (A && !B) |-> (sum && !carry_out)
    );

    // A low and B high must produce sum high and carry low.
    check_a_low_b_high: assert property (
        @(posedge clk) (!A && B) |-> (sum && !carry_out)
    );

    // Both inputs high must produce carry high and sum low.
    check_both_high: assert property (
        @(posedge clk) (A && B) |-> (!sum && carry_out)
    );

endmodule