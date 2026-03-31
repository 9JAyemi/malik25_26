module bitwise_and_sva (
    input logic        clk,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [7:0]  C
);

    // C must equal the bitwise AND of A and B.
    check_output_matches_and: assert property (
        @(posedge clk) C == (A & B)
    );

    // If A is all zeros, C must be all zeros.
    check_zero_a_forces_zero_c: assert property (
        @(posedge clk) (A == 8'h00) |-> (C == 8'h00)
    );

    // If B is all zeros, C must be all zeros.
    check_zero_b_forces_zero_c: assert property (
        @(posedge clk) (B == 8'h00) |-> (C == 8'h00)
    );

    // If A is all ones, C must equal B.
    check_all_ones_a_passes_b: assert property (
        @(posedge clk) (A == 8'hFF) |-> (C == B)
    );

    // If B is all ones, C must equal A.
    check_all_ones_b_passes_a: assert property (
        @(posedge clk) (B == 8'hFF) |-> (C == A)
    );

    // If A and B are equal, C must equal that value.
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (A == B) |-> (C == A)
    );

    // If C is all zeros, both inputs must be all zeros.
    check_zero_output_requires_zero_inputs: assert property (
        @(posedge clk) (C == 8'h00) |-> ((A == 8'h00) && (B == 8'h00))
    );

    // If C equals A, B must be all ones.
    check_c_equals_a_requires_b_all_ones: assert property (
        @(posedge clk) (C == A) |-> (B == 8'hFF)
    );

    // If C equals B, A must be all ones.
    check_c_equals_b_requires_a_all_ones: assert property (
        @(posedge clk) (C == B) |-> (A == 8'hFF)
    );

    // If C is all ones, both inputs must be all ones.
    check_all_ones_output_requires_all_ones_inputs: assert property (
        @(posedge clk) (C == 8'hFF) |-> ((A == 8'hFF) && (B == 8'hFF))
    );

endmodule