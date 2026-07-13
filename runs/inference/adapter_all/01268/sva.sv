module half_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic sum,
    input logic carry_out
);

    // sum must equal the XOR of A and B.
    check_sum_xor: assert property (
        @(posedge clk) sum == (A ^ B)
    );

    // carry_out must equal the AND of A and B.
    check_carry_and: assert property (
        @(posedge clk) carry_out == (A & B)
    );

    // When both inputs are low, sum is low and carry_out is low.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B) |-> (!sum && !carry_out)
    );

    // When only A is high, sum is high and carry_out is low.
    check_a_only: assert property (
        @(posedge clk) (A && !B) |-> (sum && !carry_out)
    );

    // When only B is high, sum is high and carry_out is low.
    check_b_only: assert property (
        @(posedge clk) (!A && B) |-> (sum && !carry_out)
    );

    // When both inputs are high, sum is low and carry_out is high.
    check_both_high: assert property (
        @(posedge clk) (A && B) |-> (!sum && carry_out)
    );

endmodule