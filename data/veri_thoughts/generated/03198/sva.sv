module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

    // Sum is the XOR of A, B, and Ci.
    check_sum_function: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

    // Carry-out matches the implemented generate/propagate equation.
    check_carry_function: assert property (
        @(posedge clk) Co == ((A & B) | ((A ^ B) & Ci))
    );

    // With Ci low, the adder behaves as a half adder.
    check_half_adder_mode: assert property (
        @(posedge clk) !Ci |-> ((S == (A ^ B)) && (Co == (A & B)))
    );

    // With Ci high, sum inverts A^B and carry is A or B.
    check_carry_in_mode: assert property (
        @(posedge clk) Ci |-> ((S == ~(A ^ B)) && (Co == (A | B)))
    );

    // When A and B match, sum follows Ci and carry follows A.
    check_equal_inputs_behavior: assert property (
        @(posedge clk) !(A ^ B) |-> ((S == Ci) && (Co == A))
    );

    // When A and B differ, sum is the inverse of Ci and carry follows Ci.
    check_unequal_inputs_behavior: assert property (
        @(posedge clk) (A ^ B) |-> ((S == ~Ci) && (Co == Ci))
    );

endmodule