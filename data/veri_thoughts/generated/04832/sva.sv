module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Cin,
    input logic S,
    input logic Cout
);

    // Sum matches the XOR of all three inputs.
    check_sum_xor: assert property (
        @(posedge clk) S == ((A ^ B) ^ Cin)
    );

    // Carry-out matches the implemented carry equation.
    check_cout_equation: assert property (
        @(posedge clk) Cout == ((A & B) | (Cin & (A ^ B)))
    );

    // The outputs equal the 2-bit arithmetic sum of the inputs.
    check_arithmetic_result: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + {1'b0, Cin})
    );

    // No asserted inputs produces zero sum and zero carry.
    check_zero_case: assert property (
        @(posedge clk) (!A && !B && !Cin) |-> (!S && !Cout)
    );

    // Exactly one asserted input produces sum without carry.
    check_one_high_case: assert property (
        @(posedge clk) ((A && !B && !Cin) || (!A && B && !Cin) || (!A && !B && Cin)) |-> (S && !Cout)
    );

    // Exactly two asserted inputs produces carry without sum.
    check_two_high_case: assert property (
        @(posedge clk) ((A && B && !Cin) || (A && !B && Cin) || (!A && B && Cin)) |-> (!S && Cout)
    );

    // All three asserted inputs produces both sum and carry.
    check_all_high_case: assert property (
        @(posedge clk) (A && B && Cin) |-> (S && Cout)
    );

endmodule