module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

    // Sum matches the XOR of the three inputs.
    check_sum_function: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

    // Carry matches the majority function of the three inputs.
    check_carry_function: assert property (
        @(posedge clk) Co == ((A & B) | (A & Ci) | (B & Ci))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B && !Ci) |-> (!S && !Co)
    );

    // Any single high input produces sum high and carry low.
    check_single_high_input: assert property (
        @(posedge clk)
        (( A && !B && !Ci) ||
         (!A &&  B && !Ci) ||
         (!A && !B &&  Ci)) |-> ( S && !Co)
    );

    // Any two high inputs produce sum low and carry high.
    check_two_high_inputs: assert property (
        @(posedge clk)
        (( A &&  B && !Ci) ||
         ( A && !B &&  Ci) ||
         (!A &&  B &&  Ci)) |-> (!S && Co)
    );

    // All-high inputs produce sum high and carry high.
    check_all_high_inputs: assert property (
        @(posedge clk) (A && B && Ci) |-> (S && Co)
    );

endmodule