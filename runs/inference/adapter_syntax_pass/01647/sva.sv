module bitwise_and_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);

    // C must always equal the bitwise AND of A and B.
    check_output_matches_and: assert property (
        @($global_clock) C == (A & B)
    );

    // C can only have bits set where both inputs have bits set.
    check_output_subset_of_inputs: assert property (
        @($global_clock) (C & ~A) == 8'h00 && (C & ~B) == 8'h00
    );

    // A zero input must force the output to zero.
    check_zero_input_forces_zero_output: assert property (
        @($global_clock) ((A == 8'h00) || (B == 8'h00)) |-> (C == 8'h00)
    );

    // A all-ones input must pass B through to the output.
    check_all_ones_input_passthrough: assert property (
        @($global_clock) ((A == 8'hFF) || (B == 8'hFF)) |-> (C == B)
    );

endmodule