module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

// Sum output matches the three-input XOR of the inputs.
    check_sum_function: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

// Carry output matches the implemented carry equation.
    check_carry_function: assert property (
        @(posedge clk) Co == ((A & B) | ((A ^ B) & Ci))
    );

// All-zero inputs produce zero sum and zero carry.
    check_zero_case: assert property (
        @(posedge clk) (!A && !B && !Ci) |-> (!S && !Co)
    );

// Any single high input produces sum high and carry low.
    check_single_high_case: assert property (
        @(posedge clk)
        ((A && !B && !Ci) || (!A && B && !Ci) || (!A && !B && Ci))
        |-> (S && !Co)
    );

// Any two high inputs produce sum low and carry high.
    check_two_high_case: assert property (
        @(posedge clk)
        ((A && B && !Ci) || (A && !B && Ci) || (!A && B && Ci))
        |-> (!S && Co)
    );

// All-high inputs produce sum high and carry high.
    check_all_high_case: assert property (
        @(posedge clk) (A && B && Ci) |-> (S && Co)
    );

endmodule
