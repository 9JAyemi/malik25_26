module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Cin,
    input logic S,
    input logic Cout
);

    // Sum output matches the XOR of all three inputs.
    check_sum_function: assert property (
        @(posedge clk) S == (A ^ B ^ Cin)
    );

    // Carry output matches the implemented carry equation.
    check_carry_function: assert property (
        @(posedge clk) Cout == ((A & B) | ((A ^ B) & Cin))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !Cin) |-> (!S && !Cout)
    );

    // Any single high input produces sum high and carry low.
    check_single_one_case: assert property (
        @(posedge clk)
        ((A && !B && !Cin) || (!A && B && !Cin) || (!A && !B && Cin))
        |-> (S && !Cout)
    );

    // Any two high inputs produce sum low and carry high.
    check_two_ones_case: assert property (
        @(posedge clk)
        ((A && B && !Cin) || (A && !B && Cin) || (!A && B && Cin))
        |-> (!S && Cout)
    );

    // All-one inputs produce sum high and carry high.
    check_all_one_case: assert property (
        @(posedge clk) (A && B && Cin) |-> (S && Cout)
    );

    // With Cin low, the block behaves like a half adder.
    check_half_adder_mode: assert property (
        @(posedge clk) !Cin |-> ((S == (A ^ B)) && (Cout == (A & B)))
    );

    // With Cin high, carry reduces to OR of A and B.
    check_cin_high_mode: assert property (
        @(posedge clk) Cin |-> ((S == ~(A ^ B)) && (Cout == (A | B)))
    );

endmodule