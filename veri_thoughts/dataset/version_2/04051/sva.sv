module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Cin,
    input logic S,
    input logic Cout
);

    // Sum matches the three-input XOR equation.
    check_sum_equation: assert property (
        @(posedge clk) (S == (A ^ B ^ Cin))
    );

    // Carry matches the implemented carry equation.
    check_carry_equation: assert property (
        @(posedge clk) (Cout == ((A & B) | (Cin & (A ^ B))))
    );

    // 000 produces zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !Cin) |-> (!S && !Cout)
    );

    // 100 produces sum one and no carry.
    check_only_a_high_case: assert property (
        @(posedge clk) (A && !B && !Cin) |-> (S && !Cout)
    );

    // 010 produces sum one and no carry.
    check_only_b_high_case: assert property (
        @(posedge clk) (!A && B && !Cin) |-> (S && !Cout)
    );

    // 001 produces sum one and no carry.
    check_only_cin_high_case: assert property (
        @(posedge clk) (!A && !B && Cin) |-> (S && !Cout)
    );

    // 110 produces zero sum and carry one.
    check_a_b_high_case: assert property (
        @(posedge clk) (A && B && !Cin) |-> (!S && Cout)
    );

    // 101 produces zero sum and carry one.
    check_a_cin_high_case: assert property (
        @(posedge clk) (A && !B && Cin) |-> (!S && Cout)
    );

    // 011 produces zero sum and carry one.
    check_b_cin_high_case: assert property (
        @(posedge clk) (!A && B && Cin) |-> (!S && Cout)
    );

    // 111 produces sum one and carry one.
    check_all_high_case: assert property (
        @(posedge clk) (A && B && Cin) |-> (S && Cout)
    );

endmodule