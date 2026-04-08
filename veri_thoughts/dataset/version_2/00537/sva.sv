module three_input_full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic S,
    input logic Cout
);

    // Sum output is the XOR of all three inputs.
    check_sum_function: assert property (
        @(posedge clk) S == (A ^ B ^ C)
    );

    // Carry output matches the implemented carry equation.
    check_carry_function: assert property (
        @(posedge clk) Cout == ((A & B) | ((A ^ B) & C))
    );

    // With C low, the block behaves as a half-adder on A and B.
    check_half_adder_mode: assert property (
        @(posedge clk) !C |-> ((S == (A ^ B)) && (Cout == (A & B)))
    );

    // With C high, sum inverts A^B and carry is the OR of A and B.
    check_c_high_mode: assert property (
        @(posedge clk) C |-> ((S == ~(A ^ B)) && (Cout == (A | B)))
    );

    // When A and B match, sum follows C and carry follows A.
    check_equal_ab_behavior: assert property (
        @(posedge clk) (A == B) |-> ((S == C) && (Cout == A))
    );

    // When A and B differ, sum is inverted C and carry follows C.
    check_different_ab_behavior: assert property (
        @(posedge clk) (A != B) |-> ((S == ~C) && (Cout == C))
    );

endmodule