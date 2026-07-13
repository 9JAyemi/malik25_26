module two_bit_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Cin,
    input logic S,
    input logic Cout
);

    // Sum equals the XOR of the three inputs.
    check_sum_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        S == (A ^ B ^ Cin)
    );

    // Carry equals the full-adder carry function.
    check_carry_equation: assert property (
        @(posedge clk) disable iff (1'b0)
        Cout == ((A & B) | (Cin & (A ^ B)))
    );

    // With Cin low, the adder behaves like a half adder.
    check_cin_low_half_adder: assert property (
        @(posedge clk) disable iff (1'b0)
        (Cin == 1'b0) |-> ((S == (A ^ B)) && (Cout == (A & B)))
    );

    // With Cin high, sum is XNOR and carry is OR.
    check_cin_high_behavior: assert property (
        @(posedge clk) disable iff (1'b0)
        (Cin == 1'b1) |-> ((S == ~(A ^ B)) && (Cout == (A | B)))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_all_zero_inputs: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A && !B && !Cin) |-> (!S && !Cout)
    );

    // All-one inputs produce sum one and carry one.
    check_all_one_inputs: assert property (
        @(posedge clk) disable iff (1'b0)
        (A && B && Cin) |-> (S && Cout)
    );

    // Any one-high input pattern produces sum one and no carry.
    check_single_high_input_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A && !B && !Cin) || (!A && B && !Cin) || (!A && !B && Cin))
        |-> (S && !Cout)
    );

    // Any two-high input pattern produces no sum and carry one.
    check_two_high_input_case: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A && B && !Cin) || (A && !B && Cin) || (!A && B && Cin))
        |-> (!S && Cout)
    );

endmodule