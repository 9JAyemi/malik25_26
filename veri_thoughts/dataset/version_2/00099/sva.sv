module four_input_module_sva (
    input logic [1:0] A,
    input logic [1:0] B,
    input logic X
);

    // X must equal the XOR of A's AND term and B's OR term.
    check_x_matches_logic: assert property (
        @($global_clock) X == ((A[0] & A[1]) ^ (B[0] | B[1]))
    );

    // If only the A AND term is high, X must be high.
    check_x_high_when_only_a_term_high: assert property (
        @($global_clock) ((A[0] & A[1]) && !(B[0] | B[1])) |-> (X == 1'b1)
    );

    // If only the B OR term is high, X must be high.
    check_x_high_when_only_b_term_high: assert property (
        @($global_clock) (!(A[0] & A[1]) && (B[0] | B[1])) |-> (X == 1'b1)
    );

    // If both terms are low, X must be low.
    check_x_low_when_both_terms_low: assert property (
        @($global_clock) (!(A[0] & A[1]) && !(B[0] | B[1])) |-> (X == 1'b0)
    );

    // If both terms are high, X must be low.
    check_x_low_when_both_terms_high: assert property (
        @($global_clock) ((A[0] & A[1]) && (B[0] | B[1])) |-> (X == 1'b0)
    );

endmodule