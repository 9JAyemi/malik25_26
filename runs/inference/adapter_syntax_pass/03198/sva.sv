module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Ci,
    input logic S,
    input logic Co
);

    // Sum matches the XOR of the three inputs.
    check_sum_matches_xor: assert property (
        @(posedge clk) S == (A ^ B ^ Ci)
    );

    // Carry-out matches the implemented carry equation.
    check_carry_matches_and_or: assert property (
        @(posedge clk) Co == ((A & B) | ((A ^ B) & Ci))
    );

    // Carry-out is high when both data inputs are high.
    check_carry_high_when_both_data_high: assert property (
        @(posedge clk) (A & B) |-> Co
    );

    // Carry-out is high when the two data inputs differ and carry-in is high.
    check_carry_high_when_data_differs_and_cin_high: assert property (
        @(posedge clk) ((A ^ B) & Ci) |-> Co
    );

    // Carry-out is low when the two data inputs are equal.
    check_carry_low_when_data_equal: assert property (
        @(posedge clk) (A == B) |-> !Co
    );

    // Carry-out is low when the two data inputs differ and carry-in is low.
    check_carry_low_when_data_differs_and_cin_low: assert property (
        @(posedge clk) ((A ^ B) & !Ci) |-> !Co
    );

endmodule