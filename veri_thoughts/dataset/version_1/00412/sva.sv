module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

    // Sum output is the XOR of the three inputs.
    check_sum_xor: assert property (
        @(posedge clk) (S == (A ^ B ^ Ci))
    );

    // Carry output matches the implemented carry equation.
    check_carry_logic: assert property (
        @(posedge clk) (Co == ((A & B) | ((A ^ B) & Ci)))
    );

    // The output pair equals the 2-bit arithmetic sum of the inputs.
    check_binary_sum: assert property (
        @(posedge clk) ({Co, S} == ({1'b0, A} + {1'b0, B} + {1'b0, Ci}))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_zero_case: assert property (
        @(posedge clk)
        ((A == 1'b0) && (B == 1'b0) && (Ci == 1'b0))
        |-> ((S == 1'b0) && (Co == 1'b0))
    );

    // Exactly one high input produces sum without carry.
    check_single_one_case: assert property (
        @(posedge clk)
        (((A == 1'b1) && (B == 1'b0) && (Ci == 1'b0)) ||
         ((A == 1'b0) && (B == 1'b1) && (Ci == 1'b0)) ||
         ((A == 1'b0) && (B == 1'b0) && (Ci == 1'b1)))
        |-> ((S == 1'b1) && (Co == 1'b0))
    );

    // Exactly two high inputs produce carry without sum.
    check_two_one_case: assert property (
        @(posedge clk)
        (((A == 1'b1) && (B == 1'b1) && (Ci == 1'b0)) ||
         ((A == 1'b1) && (B == 1'b0) && (Ci == 1'b1)) ||
         ((A == 1'b0) && (B == 1'b1) && (Ci == 1'b1)))
        |-> ((S == 1'b0) && (Co == 1'b1))
    );

    // All-one inputs produce both sum and carry.
    check_all_one_case: assert property (
        @(posedge clk)
        ((A == 1'b1) && (B == 1'b1) && (Ci == 1'b1))
        |-> ((S == 1'b1) && (Co == 1'b1))
    );

endmodule