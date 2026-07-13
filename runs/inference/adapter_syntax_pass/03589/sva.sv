module addsub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] OUT,
    input logic COUT
);

    // COUT is the sign bit of the selected add/sub result.
    check_cout_matches_selected_result: assert property (
        @($global_clock)
        COUT == (SUB ? (A + (~B) + 4'd1)[3] : (A + B)[3])
    );

    // OUT matches the selected add/sub result.
    check_out_matches_selected_result: assert property (
        @($global_clock)
        OUT == (SUB ? (B + 4'd1) : (A + B))
    );

    // In add mode, OUT is the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @($global_clock)
        !SUB |-> (OUT == (A + B))
    );

    // In subtract mode, OUT is the 4-bit sum of B and 1.
    check_sub_mode_result: assert property (
        @($global_clock)
        SUB |-> (OUT == (B + 4'd1))
    );

    // In add mode, COUT is the sign bit of A+B.
    check_add_mode_cout: assert property (
        @($global_clock)
        !SUB |-> (COUT == ((A + B)[3]))
    );

    // In subtract mode, COUT is the sign bit of A.
    check_sub_mode_cout: assert property (
        @($global_clock)
        SUB |-> (COUT == A[3])
    );

    // In add mode, OUT is never negative.
    check_add_mode_nonnegative: assert property (
        @($global_clock)
        !SUB |-> (OUT[3] == 1'b0)
    );

    // In subtract mode, OUT is always positive.
    check_sub_mode_positive: assert property (
        @($global_clock)
        SUB |-> (OUT[3] == 1'b0)
    );

    // In add mode, COUT matches A[3].
    check_add_mode_cout_matches_a_sign: assert property (
        @($global_clock)
        !SUB |-> (COUT == A[3])
    );

    // In subtract mode, COUT matches B[3].
    check_sub_mode_cout_matches_b_sign: assert property (
        @($global_clock)
        SUB |-> (COUT == B[3])
    );

endmodule