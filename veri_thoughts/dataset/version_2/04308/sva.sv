module sky130_fd_sc_ms__or2b_sva (
    input logic X,
    input logic A,
    input logic B_N
);

    // Output implements A OR inverted B_N.
    check_output_function: assert property (
        @($global_clock) X == (A | ~B_N)
    );

    // When B_N is high, the output reduces to A.
    check_b_n_high_passes_a: assert property (
        @($global_clock) B_N |-> (X == A)
    );

    // When B_N is low, inversion forces the output high.
    check_b_n_low_forces_high: assert property (
        @($global_clock) !B_N |-> (X == 1'b1)
    );

    // When A is low, the output matches the inversion of B_N.
    check_a_low_matches_inverted_b_n: assert property (
        @($global_clock) !A |-> (X == ~B_N)
    );

    // A low output occurs only for A low and B_N high.
    check_low_output_only_on_single_case: assert property (
        @($global_clock) !X |-> (!A && B_N)
    );

endmodule